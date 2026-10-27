(* insert_relaxed_queue.v, ported from aspect-oriented queue linearizability *)
(* Adapts insert_relaxed_stack.v for queues *)


From iris_logatom.pure_logic.aspect.queue.ext Require Import conc_his_rel.

Section insert_relaxed_queue.
  Context `{abstract_queue_model}.
  Implicit Types (pre val : relation operation).

  (* InsertRelaxedQueue: A queue where dequeue operations are totally ordered
     and enqueue-dequeue pairs respect FIFO ordering.

     Key difference from stack:
     - Stack uses LIFO: ir_ooo gives pre rb ra (later enqueue's dequeue comes first)
     - Queue uses FIFO: ir_ooo gives pre ra rb (earlier enqueue's dequeue comes first)
  *)
  Class InsertRelaxedQueue pre val := {
    #[local] ir_queue_wellformed :: WellformedHistory pre val;
    dequeue_ordered a b : is_pop val a → is_pop val b → a ≠ b → pre a b ∨ pre b a;
    enqueue_dequeue_ordered a b : is_push val a → is_pop val b → pre a b ∨ pre b a;
    (* FIFO ordering: if enq(ia) < enq(ib) and enq(ib) < deq(ra), then deq(ra) < deq(rb)
       This ensures first-in-first-out behavior *)
    ir_ooo ia ra ib rb : val ia ra → val ib rb → pre ia ib → pre ib ra → pre ra rb;
  }.

  Context pre val `{!InsertRelaxedQueue pre val}.

  (* Make parent class instances available for typeclass resolution *)
  #[local] Existing Instance ir_queue_wellformed.
  #[local] Existing Instance wf_pre_transitive.
  #[local] Existing Instance wf_pre_antisymmetric.
  #[local] Existing Instance wf_pre_irreflexive.

  (* The witness relation for constructing the linearization *)
  Definition witness : relation operation :=
    λ a b, pre a b ∨
           (∃ ra rb, val a ra ∧ val b rb ∧
             (* For FIFO: if ra comes before b (dequeue before enqueue), then a < b *)
             (pre ra b ∨
              (* Or: complex case involving FIFO ordering *)
              (pre a rb ∧ pre b ra ∧ pre ra rb))).

  Lemma witnessI1 a b : pre a b → witness a b.
  Proof. left. done. Qed.

  Lemma witnessI2 a ra b rb : val a ra → val b rb → pre ra b → witness a b.
  Proof.
    intros Hva Hvb Hrab.
    right. exists ra, rb. split; first done. split; first done. left. done.
  Qed.

  Lemma witnessI3 a ra b rb :
    val a ra → val b rb → pre a rb → pre b ra → pre ra rb → witness a b.
  Proof.
    intros Hva Hvb Harb Hbra Hrarb.
    right. exists ra, rb. split; first done. split; first done. right. done.
  Qed.

  Lemma witnessD a b : witness a b →
    pre a b ∨
    (∃ ra rb, val a ra ∧ val b rb ∧ pre ra b) ∨
    (∃ ra rb, val a ra ∧ val b rb ∧ pre a rb ∧ pre b ra ∧ pre ra rb).
  Proof.
    intros [Hpre|(ra & rb & Hva & Hvb & [Hrab|(Harb & Hbra & Hrarb)])].
    - left. done.
    - right. left. exists ra, rb. done.
    - right. right. exists ra, rb. done.
  Qed.

  Lemma lem_val_then_pr ia ra : val ia ra → pre ia ra.
  Proof.
    intros Hval.
    destruct (enqueue_dequeue_ordered ia ra) as [Hir|Hri].
    - exists ra. done.
    - exists ia. done.
    - done.
    - exfalso. eapply def_val_then_not_pr; eauto.
  Qed.

  Lemma lem_val_then_not_witness ia ra : val ia ra → ¬ witness ra ia.
  Proof.
    intros Hval Hw.
    apply witnessD in Hw.
    destruct Hw as [Hpre|[(rx & rix & Hvr & Hvi & Hpre)|(rx & rix & Hvr & Hvi & H1 & H2 & H3)]].
    - eapply def_val_then_not_pr; eauto.
    - eapply def_val_order; first exact Hval. exists rx. right. done.
    - eapply def_val_order; first exact Hval. exists rx. right. done.
  Qed.

  Lemma lem_witness_irreflexive : Irreflexive witness.
  Proof.
    intros a Haa.
    apply witnessD in Haa.
    destruct Haa as [Hpre|[(ra & rb & Hva & Hvb & Hpre)|(ra & rb & Hva & Hvb & H1 & H2 & H3)]].
    - by eapply wf_pre_irreflexive.
    - exact (def_val_then_not_pr _ _ Hva Hpre).
    - pose proof (def_dequeue_once _ _ _ Hva Hvb) as Heq. subst rb.
      exact (wf_pre_irreflexive _ H3).
  Qed.

  Lemma lem_pr_in_witness : subrelation pre witness.
  Proof. intros a b. apply witnessI1. Qed.

  Lemma lem_witness_total_on_dequeue a b :
    is_pop val a → is_pop val b → a ≠ b → witness a b ∨ witness b a.
  Proof.
    intros Ha Hb Hneq.
    destruct (dequeue_ordered a b Ha Hb Hneq) as [Hab|Hba]; [left|right]; by apply witnessI1.
  Qed.

  Lemma lem_witness_total_on_enqueue_dequeue a b :
    is_push val a → is_pop val b → witness a b ∨ witness b a.
  Proof.
    intros Ha Hb.
    destruct (enqueue_dequeue_ordered a b Ha Hb) as [Hab|Hba]; [left|right]; by apply witnessI1.
  Qed.

  Lemma lem_witness_total_on_enqueue a b :
    is_push val a → is_push val b → a ≠ b → witness a b ∨ witness b a.
  Proof.
    intros [ra Hva] [rb Hvb] Hneq.
    destruct (enqueue_dequeue_ordered a rb) as [Harb|Hrba].
    - exists ra. done.
    - exists b. done.
    - destruct (enqueue_dequeue_ordered b ra) as [Hbra|Hrab].
      + exists rb. done.
      + exists a. done.
      + (* pre a rb, pre b ra *)
        assert (Hra : is_pop val ra) by (exists a; done).
        assert (Hrb : is_pop val rb) by (exists b; done).
        destruct (decide (ra = rb)) as [Heq|Hneq_r].
        * subst rb. exfalso. apply Hneq. eapply def_enqueue_once; eauto.
        * destruct (dequeue_ordered ra rb Hra Hrb Hneq_r) as [Hrarb|Hrbra].
          -- (* For FIFO: pre ra rb means a's dequeue comes first, so a < b *)
             left. eapply (witnessI3 a ra b rb); done.
          -- (* For FIFO: pre rb ra means b's dequeue comes first, so b < a *)
             right. eapply (witnessI3 b rb a ra); done.
      + (* pre ra b *)
        left. eapply (witnessI2 a ra b rb); done.
    - (* pre rb a *)
      right. eapply (witnessI2 b rb a ra); done.
  Qed.

  (* Helper for common contradiction pattern in transitivity proof:
     If we have witness-case-3 data for (a,b) and pre b a, contradiction. *)
  Local Lemma ir_contra a b ra rb :
    val a ra → val b rb → pre a rb → pre b ra → pre ra rb → pre b a → False.
  Proof.
    intros Hva Hvb Harb Hbra Hrarb Hba.
    (* For FIFO: ir_ooo gives pre ra rb when pre b a, pre a rb
       But we already have pre ra rb, and pre rb ra would give contradiction *)
    assert (pre rb ra) by (eapply ir_ooo; eauto).
    assert (ra = rb) by (by eapply wf_pre_antisymmetric).
    subst. assert (a = b) by (eapply def_enqueue_once; eauto).
    subst. by eapply wf_pre_irreflexive.
  Qed.

  (* Helper: ir_ooo with antisymmetry gives contradiction *)
  Local Lemma ir_ooo_contra a b ra rb :
    val a ra → val b rb → pre b a → pre a rb → pre ra rb → False.
  Proof.
    intros Hva Hvb Hba Harb Hrarb.
    (* ir_ooo: val b rb, val a ra, pre b a, pre a rb → pre rb ra *)
    assert (pre rb ra) by (eapply ir_ooo; eauto).
    assert (ra = rb) by (by eapply wf_pre_antisymmetric).
    subst. by eapply wf_pre_irreflexive.
  Qed.

  Lemma lem_witness_transitive : Transitive witness.
  Proof.
    intros x y z Hxy Hyz.
    apply witnessD in Hxy.
    apply witnessD in Hyz.
    destruct Hxy as [Hxy|[(rx & ry & Hvx & Hvy & Hrxy)|(rx & ry & Hvx & Hvy & Hxry & Hyrx & Hrxry)]];
    destruct Hyz as [Hyz|[(ry' & rz & Hvy' & Hvz & Hry'z)|(ry' & rz & Hvy' & Hvz & Hyrz & Hzry' & Hrzry')]].

    - (* (1,1) pre x y, pre y z *)
      apply witnessI1. by etrans.

    - (* (1,2) pre x y; val y ry', val z rz, pre ry' z *)
      apply witnessI1.
      etrans; first exact Hxy.
      etrans; first exact (lem_val_then_pr _ _ Hvy'). exact Hry'z.

    - (* (1,3) pre x y; val y ry', val z rz, pre y rz, pre z ry', pre rz ry' *)
      (* We have pre z ry' and pre ry' rz, so pre z rz
         But that's expected from val z rz. The key insight is that
         we can construct witness x z via witnessI1 using transitivity *)
      (* Case analysis on what x is *)
      destruct (def_enqueue_or_dequeue x y Hxy) as [[cx [Hvcx|Hcvx]] _].
      + (* x is enqueue: val x cx *)
        destruct (enqueue_dequeue_ordered z cx) as [Hzcx|Hcxz];
          [exists rz; done|exists x; done| |by eapply witnessI2].
        (* pre z cx *)
        destruct (decide (cx = rz)) as [Heq|Hneq].
        * (* cx = rz → val x rz and val z rz → x = z by def_enqueue_once *)
          subst cx.
          assert (Hxz : x = z) by (eapply def_enqueue_once; [exact Hvcx | exact Hvz]).
          subst x.
          (* Use ir_ooo to derive a contradiction:
             ir_ooo z rz y ry': val z rz, val y ry', pre z y, pre y rz → pre rz ry'
             Combined with pre ry' rz gives ry' = rz by antisymmetry.
             Then val y rz and val z rz gives y = z.
             So pre z y becomes pre z z, which contradicts irreflexivity. *)
          exfalso.
          assert (Hrz_ry' : pre rz ry') by (eapply ir_ooo; [exact Hvz | exact Hvy' | exact Hxy | exact Hyrz]).
          assert (Heq : ry' = rz) by (eapply wf_pre_antisymmetric; [exact Hrzry' | exact Hrz_ry']).
          subst ry'.
          assert (Hyz : y = z) by (eapply def_enqueue_once; [exact Hvy' | exact Hvz]).
          subst y.
          (* Now Hxy : pre z z, which contradicts irreflexivity *)
          eapply wf_pre_irreflexive. exact Hxy.
        * (* cx ≠ rz *)
          assert (Hcx_deq : is_pop val cx) by (exists x; done).
          assert (Hrz_deq : is_pop val rz) by (exists z; done).
          destruct (dequeue_ordered cx rz Hcx_deq Hrz_deq Hneq) as [Hcxrz|Hrzcx].
          -- (* pre cx rz *)
             eapply (witnessI3 x cx z rz); try done.
             ++ (* pre x rz *) etrans; first exact Hxy. exact Hyrz.
          -- (* pre rz cx → contradiction via ir_ooo *)
             exfalso.
             (* From pre ry' rz (Hrzry') and pre rz cx: pre ry' cx *)
             assert (Hry'cx : pre ry' cx) by (etrans; [exact Hrzry' | exact Hrzcx]).
             (* From pre y rz and pre rz cx: pre y cx *)
             assert (Hycx : pre y cx) by (etrans; [exact Hyrz | exact Hrzcx]).
             (* ir_ooo: val x cx, val y ry', pre x y, pre y cx → pre cx ry' *)
             assert (Hcxry' : pre cx ry') by (eapply ir_ooo; eauto).
             (* pre cx ry' and pre ry' cx → cx = ry' *)
             assert (Heq : cx = ry') by (eapply wf_pre_antisymmetric; [exact Hcxry' | exact Hry'cx]).
             subst ry'.
             (* val x cx and val y cx → x = y *)
             assert (Hxy_eq : x = y) by (eapply def_enqueue_once; eauto).
             subst x.
             (* pre y y contradicts irreflexivity *)
             eapply wf_pre_irreflexive. exact Hxy.
      + (* x is dequeue: val cx x *)
        destruct (enqueue_dequeue_ordered z x) as [Hzx|Hxz];
          [exists rz; done|exists cx; done| |apply witnessI1; done].
        (* pre z x → contradiction via ir_ooo *)
        exfalso.
        (* From pre z x and pre x y: pre z y *)
        assert (Hzy : pre z y) by (etrans; [exact Hzx | exact Hxy]).
        (* ir_ooo: val z rz, val y ry', pre z y, pre y rz → pre rz ry' *)
        assert (Hrzry'2 : pre rz ry') by (eapply ir_ooo; eauto).
        (* pre rz ry' and pre ry' rz (Hrzry') → rz = ry' *)
        assert (Heq : rz = ry') by (eapply wf_pre_antisymmetric; [exact Hrzry'2 | exact Hrzry']).
        subst ry'.
        (* val z rz and val y rz → z = y *)
        assert (Hzy_eq : z = y) by (eapply def_enqueue_once; eauto).
        subst z.
        (* pre y y contradicts irreflexivity *)
        eapply wf_pre_irreflexive. exact Hzy.

    - (* (2,1) val x rx, val y ry, pre rx y; pre y z *)
      apply witnessI1.
      etrans; first exact (lem_val_then_pr _ _ Hvx).
      etrans; first exact Hrxy. exact Hyz.

    - (* (2,2) val x rx, val y ry, pre rx y; val y ry', val z rz, pre ry' z *)
      pose proof (def_dequeue_once _ _ _ Hvy Hvy') as ->. rename ry' into ry.
      eapply (witnessI2 x rx z rz); try done.
      etrans; first exact Hrxy.
      etrans; first exact (lem_val_then_pr _ _ Hvy). exact Hry'z.

    - (* (2,3) val x rx, val y ry, pre rx y; val y ry', val z rz, pre y rz, pre z ry', pre rz ry' *)
      pose proof (def_dequeue_once _ _ _ Hvy Hvy') as ->. rename ry' into ry.
      destruct (enqueue_dequeue_ordered z rx) as [Hzrx|Hrxz];
        [exists rz; done|exists x; done| |by eapply witnessI2].
      (* pre z rx *)
      destruct (decide (rx = ry)) as [->|Hneq].
      + (* rx = ry → x = y → contradiction *)
        exfalso. assert (x = y) by (eapply def_enqueue_once; eauto).
        subst. eapply wf_pre_irreflexive.
        etrans; first exact Hrxy. exact (lem_val_then_pr _ _ Hvy).
      + destruct (dequeue_ordered rx ry) as [Hrxry|Hryrx];
          [exists x; done|exists y; done|done| |].
        * (* pre rx ry → ir_ooo_contra *)
          exfalso. eapply (ir_ooo_contra y z ry rz); try done.
          by etrans.
        * (* pre ry rx → contradiction via cycle *)
          exfalso.
          (* pre ry rx, pre rx y, pre y ry → pre ry ry *)
          assert (Hryry : pre ry ry).
          { etrans; first exact Hryrx.
            etrans; first exact Hrxy.
            exact (lem_val_then_pr _ _ Hvy). }
          by eapply wf_pre_irreflexive.

    - (* (3,1) val x rx, val y ry, pre x ry, pre y rx, pre rx ry; pre y z *)
      destruct (def_enqueue_or_dequeue y z Hyz) as [_ [cz [Hvcz|Hczv]]].
      + (* z is enqueue: val z cz *)
        destruct (enqueue_dequeue_ordered z rx) as [Hzrx|Hrxz];
          [exists cz; done|exists x; done| |by eapply witnessI2].
        (* pre z rx *)
        destruct (enqueue_dequeue_ordered x cz) as [Hxcz|Hczx];
          [exists rx; done|exists z; done| |].
        * (* pre x cz *)
          destruct (enqueue_dequeue_ordered z ry) as [Hzry|Hryz];
            [exists cz; done|exists y; done| |].
          -- (* pre z ry → ir_ooo gives pre ry cz for FIFO *)
             assert (pre ry cz) by (eapply ir_ooo; eauto).
             eapply (witnessI3 x rx z cz); try done.
             by etrans.
          -- (* pre ry z → pre x z by trans → witnessI1 *)
             apply witnessI1. etrans; first exact Hxry. exact Hryz.
        * (* pre cz x → pre y x → ir_contra *)
          exfalso. eapply (ir_contra x y rx ry); try done.
          etrans; first exact Hyz. etrans; first exact (lem_val_then_pr _ _ Hvcz). exact Hczx.
      + (* z is dequeue: val cz z *)
        destruct (enqueue_dequeue_ordered x z) as [Hxz|Hzx];
          [exists rx; done|exists cz; done|apply witnessI1; done|].
        (* pre z x → pre y x → ir_contra *)
        exfalso. eapply (ir_contra x y rx ry); try done.
        by etrans.

    - (* (3,2) val x rx, val y ry, pre x ry, pre y rx, pre rx ry;
              val y ry', val z rz, pre ry' z *)
      pose proof (def_dequeue_once _ _ _ Hvy Hvy') as ->. rename ry' into ry.
      destruct (enqueue_dequeue_ordered z rx) as [Hzrx|Hrxz];
        [exists rz; done|exists x; done| |by eapply witnessI2].
      (* pre z rx *)
      destruct (enqueue_dequeue_ordered x rz) as [Hxrz|Hrzx];
        [exists rx; done|exists z; done| |].
      + (* pre x rz *)
        destruct (decide (rx = rz)) as [->|Hneq].
        * (* rx = rz → x = z → pre y x → ir_contra *)
          exfalso. assert (Heq : x = z) by (eapply def_enqueue_once; eauto).
          subst. apply (ir_contra _ _ _ _ Hvx Hvy Hxry Hyrx Hrxry).
          etrans; first exact (lem_val_then_pr _ _ Hvy). exact Hry'z.
        * destruct (dequeue_ordered rx rz) as [Hrxrz|Hrzrx];
            [exists x; done|exists z; done|done| |].
          -- (* pre rx rz → use witnessI1 via pre x z *)
             apply witnessI1.
             (* pre x ry, pre ry z → pre x z *)
             etrans; first exact Hxry. exact Hry'z.
          -- (* pre rz rx → contradiction via ir_ooo *)
             exfalso.
             (* pre x ry, pre ry z → pre x z *)
             assert (Hxz : pre x z) by (etrans; first exact Hxry; exact Hry'z).
             (* ir_ooo: val x rx, val z rz, pre x z, pre z rx → pre rx rz *)
             assert (Hrxrz : pre rx rz) by (eapply ir_ooo; eauto).
             (* pre rx rz and pre rz rx → rx = rz, contradicting Hneq *)
             assert (Heq : rx = rz) by (eapply wf_pre_antisymmetric; [exact Hrxrz | exact Hrzrx]).
             done.
      + (* pre rz x → pre y x → ir_contra *)
        exfalso. eapply (ir_contra x y rx ry); try done.
        etrans; first exact (lem_val_then_pr _ _ Hvy).
        etrans; first exact Hry'z.
        etrans; first exact (lem_val_then_pr _ _ Hvz). exact Hrzx.

    - (* (3,3) val x rx, val y ry, pre x ry, pre y rx, pre rx ry;
              val y ry', val z rz, pre y rz, pre z ry', pre rz ry' *)
      pose proof (def_dequeue_once _ _ _ Hvy Hvy') as ->. rename ry' into ry.
      destruct (enqueue_dequeue_ordered z rx) as [Hzrx|Hrxz];
        [exists rz; done|exists x; done| |by eapply witnessI2].
      (* pre z rx *)
      destruct (enqueue_dequeue_ordered x rz) as [Hxrz|Hrzx];
        [exists rx; done|exists z; done| |].
      + (* pre x rz *)
        destruct (decide (rx = rz)) as [->|Hneq].
        * (* rx = rz → x = z → pre ry rz ∧ pre rz ry → ry = rz → contradiction *)
          exfalso.
          assert (x = z) by (eapply def_enqueue_once; eauto).
          subst.
          assert (rz = ry) by (by eapply wf_pre_antisymmetric).
          subst. by eapply wf_pre_irreflexive.
        * destruct (dequeue_ordered rx rz) as [Hrxrz|Hrzrx];
            [exists x; done|exists z; done|done| |].
          -- (* pre rx rz → use witnessI3 *)
             by eapply (witnessI3 x rx z rz).
          -- (* pre rz rx → contradiction via transitivity *)
             exfalso.
             (* pre rx ry, pre ry rz → pre rx rz *)
             assert (Hrxrz : pre rx rz) by (etrans; first exact Hrxry; exact Hrzry').
             (* pre rx rz and pre rz rx → rx = rz, contradicting Hneq *)
             assert (Heq : rx = rz) by (eapply wf_pre_antisymmetric; [exact Hrxrz | exact Hrzrx]).
             done.
      + (* pre rz x → pre y x → ir_contra *)
        exfalso. eapply (ir_contra x y rx ry); try done.
        etrans; first exact Hyrz. exact Hrzx.
  Qed.

  Lemma lem_witness_antisymmetric : Antisymmetric operation (=) witness.
  Proof.
    intros a b Hab Hba.
    apply witnessD in Hab.
    apply witnessD in Hba.
    destruct Hab as [Hab|[(ra & rb & Hva & Hvb & Hrab)|(ra & rb & Hva & Hvb & Harb & Hbra & Hrarb)]];
    destruct Hba as [Hba|[(rb2 & ra2 & Hvb2 & Hva2 & Hrb2a)|(rb2 & ra2 & Hvb2 & Hva2 & Hbra2 & Harb2 & Hra2rb2)]].
    - (* (1,1) pre a b, pre b a *)
      by eapply wf_pre_antisymmetric.
    - (* (1,2) pre a b; val b rb2, val a ra2, pre rb2 a *)
      exfalso. eapply def_val_then_not_pr; first exact Hvb2.
      by etrans.
    - (* (1,3) pre a b; val b rb2, val a ra2, pre b ra2, pre a rb2, pre ra2 rb2 *)
      pose proof (ir_ooo _ _ _ _ Hva2 Hvb2 Hab Hbra2) as Hrb2ra2.
      pose proof (wf_pre_antisymmetric _ _ Hra2rb2 Hrb2ra2) as Heq. subst ra2.
      eapply def_enqueue_once; eauto.
    - (* (2,1) val a ra, val b rb, pre ra b; pre b a *)
      exfalso. eapply def_val_then_not_pr; first exact Hva.
      by etrans.
    - (* (2,2) val a ra, val b rb, pre ra b; val b rb2, val a ra2, pre rb2 a *)
      pose proof (def_dequeue_once _ _ _ Hva Hva2) as ->. rename ra2 into ra.
      pose proof (def_dequeue_once _ _ _ Hvb Hvb2) as ->. rename rb2 into rb.
      eapply wf_pre_antisymmetric.
      + etrans; first exact (lem_val_then_pr _ _ Hva). exact Hrab.
      + etrans; first exact (lem_val_then_pr _ _ Hvb). exact Hrb2a.
    - (* (2,3) val a ra, val b rb, pre ra b; val b rb2, val a ra2, pre b ra2, pre a rb2, pre ra2 rb2 *)
      pose proof (def_dequeue_once _ _ _ Hva Hva2) as ->. rename ra2 into ra.
      pose proof (def_dequeue_once _ _ _ Hvb Hvb2) as ->. rename rb2 into rb.
      exfalso.
      pose proof (wf_pre_antisymmetric _ _ Hrab Hbra2) as Heq. subst ra.
      eapply def_val_order; first exact Hva. exists rb. right. done.
    - (* (3,1) val a ra, val b rb, pre a rb, pre b ra, pre ra rb; pre b a *)
      pose proof (ir_ooo _ _ _ _ Hvb Hva Hba Harb) as Hrarb'.
      pose proof (wf_pre_antisymmetric _ _ Hrarb Hrarb') as Heq. subst ra.
      eapply def_enqueue_once; eauto.
    - (* (3,2) val a ra, val b rb, pre a rb, pre b ra, pre ra rb;
              val b rb2, val a ra2, pre rb2 a *)
      pose proof (def_dequeue_once _ _ _ Hva Hva2) as ->. rename ra2 into ra.
      pose proof (def_dequeue_once _ _ _ Hvb Hvb2) as ->. rename rb2 into rb.
      exfalso.
      pose proof (wf_pre_antisymmetric _ _ Harb Hrb2a) as Heq. subst rb.
      eapply def_val_order; first exact Hva. exists b. left. done.
    - (* (3,3) val a ra, val b rb, pre a rb, pre b ra, pre ra rb;
              val b rb2, val a ra2, pre b ra2, pre a rb2, pre ra2 rb2 *)
      pose proof (def_dequeue_once _ _ _ Hva Hva2) as ->. rename ra2 into ra.
      pose proof (def_dequeue_once _ _ _ Hvb Hvb2) as ->. rename rb2 into rb.
      pose proof (wf_pre_antisymmetric _ _ Hrarb Hra2rb2) as Heq. subst ra.
      eapply def_enqueue_once; eauto.
  Qed.

  (* Helper: Abcd for witness (needed for trichotomy) *)
  Local Lemma lem_witness_abcd : Abcd witness.
  Proof.
    intros a b c d Hab Hcd.
    assert (Ha : is_push val a ∨ is_pop val a).
    { destruct (witnessD _ _ Hab) as [Hpre|[(ra & rb & Hva & _ & _)|(ra & rb & Hva & _ & _)]].
      - destruct (def_enqueue_or_dequeue _ _ Hpre) as [[ca [?|?]] _]; [left|right]; eexists; eauto.
      - left. eexists. exact Hva.
      - left. eexists. exact Hva. }
    assert (Hd : is_push val d ∨ is_pop val d).
    { destruct (witnessD _ _ Hcd) as [Hpre|[(_ & rd & _ & Hvd & _)|(_ & rd & _ & Hvd & _)]].
      - destruct (def_enqueue_or_dequeue _ _ Hpre) as [_ [cd [?|?]]]; [left|right]; eexists; eauto.
      - left. eexists. exact Hvd.
      - left. eexists. exact Hvd. }
    destruct (decide (a = d)) as [->|Hneq].
    - right. exact (lem_witness_transitive _ _ _ Hcd Hab).
    - assert (Htotal : witness a d ∨ witness d a).
      { destruct Ha as [Ha|Ha]; destruct Hd as [Hd|Hd].
        - exact (lem_witness_total_on_enqueue a d Ha Hd Hneq).
        - exact (lem_witness_total_on_enqueue_dequeue a d Ha Hd).
        - destruct (lem_witness_total_on_enqueue_dequeue d a Hd Ha) as [?|?]; [right|left]; done.
        - exact (lem_witness_total_on_dequeue a d Ha Hd Hneq). }
      destruct Htotal as [Had|Hda].
      + left. done.
      + right. exact (lem_witness_transitive _ _ _
          (lem_witness_transitive _ _ _ Hcd Hda) Hab).
  Qed.

  (* FIFO ordering theorem: the constructed linearization respects FIFO *)
  Lemma lem_witness_fifo ia ra ib rb :
    val ia ra → val ib rb → witness ia ib → witness ra rb.
  Proof.
    intros Hvia Hvib Hwiaib.
    apply witnessD in Hwiaib.
    destruct Hwiaib as [Hpre|[(ria & rib & Hvia' & Hvib' & Hriab)|
                         (ria & rib & Hvia' & Hvib' & Hiarb & Hibra & Hriarb)]].
    - (* pre ia ib *)
      (* Need to show witness ra rb *)
      (* From val ia ra and val ib rb and pre ia ib, we need FIFO property *)
      destruct (enqueue_dequeue_ordered ib ra) as [Hibra|Hraib].
      + exists rb. done.
      + exists ia. done.
      + (* pre ib ra → by ir_ooo we get pre ra rb *)
        apply witnessI1. eapply ir_ooo; eauto.
      + (* pre ra ib → need to show ra rb *)
        destruct (decide (ra = rb)) as [->|Hneq].
        * (* ra = rb → ia = ib → contradiction with ia ib ordering *)
          exfalso. assert (ia = ib) by (eapply def_enqueue_once; eauto).
          subst. by eapply wf_pre_irreflexive.
        * destruct (dequeue_ordered ra rb) as [Hrarb|Hrbra].
          -- exists ia. done.
          -- exists ib. done.
          -- intros Heq. subst. apply Hneq. reflexivity.
          -- apply witnessI1. done.
          -- (* pre rb ra and pre ra ib and pre ia ib *)
             (* This contradicts FIFO - if ia < ib, then ra < rb *)
             exfalso.
             assert (pre ia ra) by (apply lem_val_then_pr; done).
             assert (pre ib rb) by (apply lem_val_then_pr; done).
             (* pre ia ib, pre ra ib, pre rb ra *)
             (* By transitivity: pre ia ib, pre ib rb (by val), so pre ia rb *)
             (* Also pre rb ra, so pre ia ra by trans with pre ia rb, pre rb ra - but pre ia ra already *)
             (* The issue is pre ra ib and pre ib rb and pre rb ra forms a cycle *)
             assert (pre ra ra) by (etrans; first exact Hraib; etrans; [apply lem_val_then_pr; done|done]).
             by eapply wf_pre_irreflexive.
    - (* Case 2: val ia ria, val ib rib, pre ria ib *)
      pose proof (def_dequeue_once _ _ _ Hvia Hvia') as ->. rename ria into ra.
      pose proof (def_dequeue_once _ _ _ Hvib Hvib') as ->. rename rib into rb.
      (* pre ra ib, need witness ra rb *)
      destruct (decide (ra = rb)) as [->|Hneq].
      + (* ra = rb → ia = ib → pre ra ib means ... *)
        exfalso.
        assert (ia = ib) by (eapply def_enqueue_once; eauto).
        subst.
        assert (pre ib ib) by (etrans; first exact (lem_val_then_pr _ _ Hvia); exact Hriab).
        by eapply wf_pre_irreflexive.
      + destruct (dequeue_ordered ra rb) as [Hrarb|Hrbra].
        * exists ia. done.
        * exists ib. done.
        * intros Heq. subst. apply Hneq. reflexivity.
        * apply witnessI1. done.
        * (* pre rb ra and pre ra ib *)
          exfalso.
          assert (Hprerb : pre ib rb) by (apply lem_val_then_pr; done).
          assert (Hprerb' : pre ra rb) by (etrans; first exact Hriab; done).
          pose proof (wf_pre_antisymmetric _ _ Hprerb' Hrbra) as Heq. subst.
          by eapply wf_pre_irreflexive.
    - (* Case 3: val ia ria, val ib rib, pre ia rib, pre ib ria, pre ria rib *)
      pose proof (def_dequeue_once _ _ _ Hvia Hvia') as ->. rename ria into ra.
      pose proof (def_dequeue_once _ _ _ Hvib Hvib') as ->. rename rib into rb.
      (* pre ra rb directly *)
      apply witnessI1. exact Hriarb.
  Qed.

  Lemma lem_witness_sequential_set : SequentialSet witness val.
  Proof.
    constructor.
    - (* WellformedHistory *)
      constructor.
      + apply lem_witness_transitive.
      + apply lem_witness_antisymmetric.
      + apply lem_witness_irreflexive.
      + apply def_enqueue_once.
      + apply def_dequeue_once.
      + apply def_val_order.
      + (* def_enqueue_or_dequeue *)
        intros a b Hw.
        apply witnessD in Hw.
        destruct Hw as [Hpre|[(ra & rb & Hva & Hvb & _)|(ra & rb & Hva & Hvb & _)]].
        * eapply def_enqueue_or_dequeue. exact Hpre.
        * split; [exists ra|exists rb]; [left|left]; done.
        * split; [exists ra|exists rb]; [left|left]; done.
      + (* val_then_not_pr witness val *)
        intros a b Hval Hw.
        by eapply lem_val_then_not_witness.
    - (* total_on_enqueue *)
      intros a b Ha Hb Hneq.
      by apply lem_witness_total_on_enqueue.
    - (* total_on_dequeue *)
      intros a b Ha Hb Hneq.
      by apply lem_witness_total_on_dequeue.
    - (* total_on_enqueue_dequeue *)
      intros a b Ha Hb.
      by apply lem_witness_total_on_enqueue_dequeue.
  Qed.

  Lemma lem_witness_sequential_queue : SequentialQueue witness val.
  Proof.
    constructor.
    - apply lem_witness_sequential_set.
    - (* sequential_fifo *)
      unfold sequential_fifo.
      intros ia ib ra rb Hvalia Hvalib Hiaib.
      eapply lem_witness_fifo; eauto.
  Qed.

  Local Instance witness_dec `{!RelDecision pre, !RelDecision val} : RelDecision witness.
  Proof. intros a b. unfold witness. apply _. Qed.

  Theorem insert_relaxed_queue_linearizable `{!RelDecision pre, !RelDecision val} :
    ∃ prt (_ : RelDecision prt), subrelation pre prt ∧ SequentialQueue prt val.
  Proof.
    exists witness, _. split.
    - apply lem_pr_in_witness.
    - apply lem_witness_sequential_queue.
  Qed.

End insert_relaxed_queue.
