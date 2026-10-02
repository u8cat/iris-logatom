(* The stack theorem from the orders used in the TS-stack proof (Dodds, Haas, and Kirsch,
   POPL'15, Section 5.2): a visibility order vis between pushes and pops and a total order rr
   on non-empty pops.

   The paper proves Lemma 3 (vis/rr ⇒ order-correct) by iteratively repairing violating triples
   (Appendix B). We instead build a linearization of the elimination-free sub-history directly,
   by strong induction on the history: let p be the rr-last pop and x its push. If x has a
   precedence predecessor, the closure of its predecessors under precedence predecessors and
   val partners is a proper prefix that can be linearized on its own (every operation in it is
   (pre ∪ vis)-before x, by condition 2 and the maximality of p); otherwise x has no
   predecessor, p has no successor, and x ⋅ (rest) ⋅ p is a linearization. *)

From Stdlib Require Import Classical.
From iris_logatom.pure_logic.aspect.stack.ext Require Export conc_his_rel.
From iris_logatom.pure_logic.aspect.stack.ext Require Import elim_stack empty_stack.

Local Instance relation_union {A} : Union (relation A) :=
  λ r1 r2, Relation_Operators.union A r1 r2.

Section vis_rr.
  Context `{M: abstract_stack_model}.
  Implicit Types (pre val vis rr : relation operation) (empty : operation → Prop).

  (* Definition 6: the derived order ts. *)
  Definition ts_order pre vis : relation operation := λ a b,
    pre a b ∨ (∃ c, pre a c ∧ vis c b) ∨ (∃ d c, pre a d ∧ vis d c ∧ vis c b).

  (* The premises of Lemma 3. *)
  Class VisRr pre val vis rr : Prop := {
    vis_rr_alternating : alternating val vis;
    vis_rr_pr_u_vis_acyclic : Acyclic (pre ∪ vis);
    vis_rr_total a b : is_pop val a → is_pop val b → a ≠ b → rr a b ∨ rr b a;
    vis_rr_pr_u_rr_acyclic : Acyclic (pre ∪ rr);
    vis_rr_lifo ia ra ib : val ia ra → pre ia ra → ts_order pre vis ia ib → vis ib ra →
      ∃ rb, val ib rb ∧ rr rb ra;
  }.

  (* Acyclicity from ranks, for establishing the premises. *)
  Lemma acyclic_of_rank (R : relation operation) (f : operation → nat) :
    (∀ a b, R a b → f a < f b) → Acyclic R.
  Proof.
    intros Hf a Ha. cut (∀ x y, tc R x y → f x < f y); [intros Hlt; specialize (Hlt a a Ha); lia|].
    intros x y Hxy. induction Hxy as [x y Hxy|x z y Hxz _ IH]; [by apply Hf|].
    specialize (Hf _ _ Hxz). lia.
  Qed.

  (* [pre ∪ rr] is acyclic if rr increases a rank [r] on [P] that [pre] also increases on [P]. *)
  Lemma acyclic_union_rank pre rr (P : operation → Prop) (r : operation → nat) :
    Transitive pre → Irreflexive pre →
    (∀ a b, rr a b → P a ∧ P b ∧ r a < r b) →
    (∀ a b, P a → P b → pre a b → r a < r b) →
    Acyclic (pre ∪ rr).
  Proof.
    intros Htrans Hirr Hrr Hpre.
    set (T := λ x y, pre x y ∨
      ∃ p q, (x = p ∨ pre x p) ∧ P p ∧ P q ∧ r p < r q ∧ (q = y ∨ pre q y)).
    (* a pop-to-pop step through x *)
    assert (Hstep : ∀ q x p, P q → P p → (q = x ∨ pre q x) → (x = p ∨ pre x p) → r q ≤ r p).
    { intros q x p Hq Hp [->|Hqx] [<-|Hxp]; [done| |..].
      - pose proof (Hpre _ _ Hq Hp Hxp). lia.
      - pose proof (Hpre _ _ Hq Hp Hqx). lia.
      - pose proof (Hpre _ _ Hq Hp (Htrans _ _ _ Hqx Hxp)). lia. }
    assert (HT : ∀ x y, tc (pre ∪ rr) x y → T x y).
    { intros x y Hxy. induction Hxy as [x y [Hxy|Hxy]|x z y [Hxz|Hxz] _ IH].
      - by left.
      - destruct (Hrr _ _ Hxy) as (Hx & Hy & Hlt). right. exists x, y. naive_solver.
      - destruct IH as [Hzy|(p & q & Hzp & Hp & Hq & Hpq & Hqy)].
        + left. by trans z.
        + right. exists p, q. split_and!; [|done..]. right.
          destruct Hzp as [<-|Hzp]; [done|by trans z].
      - destruct (Hrr _ _ Hxz) as (Hx & Hz & Hlt).
        destruct IH as [Hzy|(p & q & Hzp & Hp & Hq & Hpq & Hqy)].
        + right. exists x, z. naive_solver.
        + right. exists x, q. split_and!; [by left|done|done| |done].
          pose proof (Hstep z z p Hz Hp (or_introl eq_refl) Hzp). lia. }
    intros x Hx. destruct (HT x x Hx) as [Hxx|(p & q & Hxp & Hp & Hq & Hpq & Hqx)].
    - by apply (Hirr x).
    - pose proof (Hstep q x p Hq Hp Hqx Hxp). lia.
  Qed.

  Definition val_closed val (S : operation → Prop) := ∀ a b, val a b → S a ↔ S b.

  (* [R] is a sequential stack history on the operations [S] that extends [pre]. *)
  Record lin_of pre val (S : operation → Prop) (R : relation operation) : Prop := {
    lin_dom a b : R a b → S a ∧ S b;
    lin_irrefl a : ¬ R a a;
    lin_trans a b c : R a b → R b c → R a c;
    lin_total a b : S a → S b → a ≠ b → R a b ∨ R b a;
    lin_pre a b : S a → S b → pre a b → R a b;
    lin_lifo : sequential_lifo R val;
  }.

  Section lemma3.
    Context pre val vis rr `{!WellformedHistory pre val} `{!VisRr pre val vis rr}.
    Hypothesis Hvp : ∀ a b, val a b → pre a b.

    #[local] Existing Instance wf_pre_transitive.
    #[local] Existing Instance wf_pre_irreflexive.

    Local Lemma pre_irrefl a : ¬ pre a a.
    Proof. apply irreflexivity, _. Qed.

    Local Lemma push_not_pop a : is_push val a → ¬ is_pop val a.
    Proof. intros [b Hab] [c Hca]. eapply def_val_order; [exact Hab|]. eauto. Qed.

    Local Lemma val_push_pop a b : val a b → is_push val a ∧ is_pop val b.
    Proof. intros Hab. split; eexists; exact Hab. Qed.

    Local Lemma vis_of_tc_pop_push q y :
      is_pop val q → is_push val y → tc (pre ∪ vis) q y → vis q y.
    Proof.
      intros Hq Hy Hqy.
      destruct (alternating_complete _ _ vis_rr_alternating y q Hy Hq) as [Hyq|]; last done.
      exfalso. apply (vis_rr_pr_u_vis_acyclic q). eapply tc_r; [exact Hqy|right; exact Hyq].
    Qed.

    Local Lemma vis_of_pre_push_pop d q : is_push val d → is_pop val q → pre d q → vis d q.
    Proof.
      intros Hd Hq Hdq.
      destruct (alternating_complete _ _ vis_rr_alternating d q Hd Hq) as [|Hqd]; first done.
      exfalso. apply (vis_rr_pr_u_vis_acyclic d).
      eapply tc_l; [left; exact Hdq|]. apply tc_once. right. exact Hqd.
    Qed.

    Local Lemma rr_asym a b : rr a b → rr b a → False.
    Proof.
      intros Hab Hba. apply (vis_rr_pr_u_rr_acyclic a).
      eapply tc_l; [right; exact Hab|]. apply tc_once. right. exact Hba.
    Qed.

    Local Lemma rr_pre_asym a b : pre a b → rr b a → False.
    Proof.
      intros Hab Hba. apply (vis_rr_pr_u_rr_acyclic a).
      eapply tc_l; [left; exact Hab|]. apply tc_once. right. exact Hba.
    Qed.

    Local Lemma rr_trans a b c : is_pop val a → is_pop val c → rr a b → rr b c → rr a c.
    Proof.
      intros Ha Hc Hab Hbc.
      destruct (decide (a = c)) as [->|Hne]; first by destruct (rr_asym _ _ Hab Hbc).
      destruct (vis_rr_total a c Ha Hc Hne) as [|Hca]; first done.
      exfalso. apply (vis_rr_pr_u_rr_acyclic a).
      eapply tc_l; [right; exact Hab|]. eapply tc_l; [right; exact Hbc|].
      apply tc_once. right. exact Hca.
    Qed.

    (* A finite set of operations containing a pop has an rr-last pop. *)
    Local Lemma rr_max (S : operation → Prop) (l : list operation) :
      (∀ o, S o → o ∈ l) → (∃ q, S q ∧ is_pop val q) →
      ∃ p, S p ∧ is_pop val p ∧ ∀ q, S q → is_pop val q → q ≠ p → rr q p.
    Proof.
      intros Hl Hne.
      cut (∀ l' : list operation, (∃ q, q ∈ l' ∧ S q ∧ is_pop val q) →
        ∃ p, S p ∧ is_pop val p ∧ ∀ q, q ∈ l' → S q → is_pop val q → q ≠ p → rr q p).
      { intros Hcut. destruct Hne as (q & Hq & Hqp).
        destruct (Hcut l) as (p & Hp & Hpp & Hmax); first by eauto.
        exists p. split_and!; [done..|]. intros q' Hq' Hq'p Hne'. by apply Hmax; [apply Hl|..]. }
      intros l'.
      induction l' as [|y l' IH]; intros (q & Hin & Hq & Hqp).
      { by apply elem_of_nil in Hin. }
      destruct (classic (∃ q, q ∈ l' ∧ S q ∧ is_pop val q)) as [Hex|Hnex].
      - destruct (IH Hex) as (p & Hp & Hpp & Hmax).
        destruct (classic (S y ∧ is_pop val y ∧ y ≠ p ∧ rr p y)) as [(Hy & Hyp & Hyne & Hpy)|Hny].
        + exists y. split_and!; [done|done|]. intros q' Hin' Hq' Hq'p Hne'.
          apply elem_of_cons in Hin' as [->|Hin']; first done.
          destruct (decide (q' = p)) as [->|Hne'']; first done.
          eapply rr_trans; [done|done|by apply Hmax|done].
        + exists p. split_and!; [done|done|]. intros q' Hin' Hq' Hq'p Hne'.
          apply elem_of_cons in Hin' as [->|Hin']; last by apply Hmax.
          destruct (vis_rr_total y p) as [|Hpq]; [done..|].
          exfalso. by apply Hny.
      - apply elem_of_cons in Hin as [->|Hin]; last by (exfalso; eauto).
        exists y. split_and!; [done|done|]. intros q' Hin' Hq' Hq'p Hne'.
        apply elem_of_cons in Hin' as [->|Hin']; first done.
        exfalso. eauto.
    Qed.

    Local Lemma lin_of_empty (S : operation → Prop) :
      (∀ o, ¬ S o) → lin_of pre val S (λ _ _, False).
    Proof.
      intros HS. split.
      - by intros ?? [].
      - by intros ? [].
      - by intros ??? [].
      - intros a ? Ha. by destruct (HS a).
      - intros a ? Ha. by destruct (HS a).
      - by intros ???? _ _ [].
    Qed.

    (* Concatenation: [D] is closed under precedence predecessors within [S]. *)
    Local Lemma lin_of_app (S D : operation → Prop) R1 R2 :
      (∀ o, D o → S o) → val_closed val D →
      (∀ a b, S a → D b → pre a b → D a) →
      lin_of pre val D R1 → lin_of pre val (λ o, S o ∧ ¬ D o) R2 →
      lin_of pre val S (λ a b, R1 a b ∨ R2 a b ∨ (D a ∧ S b ∧ ¬ D b)).
    Proof.
      intros HDS HDval HDdown HR1 HR2.
      pose proof (lin_dom _ _ _ _ HR1) as Hdom1. pose proof (lin_dom _ _ _ _ HR2) as Hdom2.
      constructor.
      - intros a b [Hab|[Hab|(Ha & Hb & _)]].
        + destruct (Hdom1 _ _ Hab). auto.
        + by destruct (Hdom2 _ _ Hab) as [[] []].
        + auto.
      - intros a [Haa|[Haa|(Ha & _ & Hna)]];
          [by eapply (lin_irrefl _ _ _ _ HR1)|by eapply (lin_irrefl _ _ _ _ HR2)|done].
      - intros a b c [Hab|[Hab|(Ha & Hb & Hnb)]] [Hbc|[Hbc|(Hb' & Hc & Hnc)]].
        + left. by eapply lin_trans.
        + by destruct (Hdom1 _ _ Hab) as [_ ?], (Hdom2 _ _ Hbc) as [[_ ?] _].
        + right; right. destruct (Hdom1 _ _ Hab). auto.
        + by destruct (Hdom2 _ _ Hab) as [_ [_ ?]], (Hdom1 _ _ Hbc).
        + right; left. by eapply lin_trans.
        + by destruct (Hdom2 _ _ Hab) as [_ [_ ?]].
        + by destruct (Hdom1 _ _ Hbc).
        + right; right. by destruct (Hdom2 _ _ Hbc) as [_ [? ?]].
        + done.
      - intros a b Ha Hb Hne.
        destruct (classic (D a)) as [Hda|Hda], (classic (D b)) as [Hdb|Hdb].
        + destruct (lin_total _ _ _ _ HR1 a b) as [|]; auto.
        + left. auto.
        + right. auto.
        + destruct (lin_total _ _ _ _ HR2 a b) as [|]; auto.
      - intros a b Ha Hb Hab.
        destruct (classic (D a)) as [Hda|Hda], (classic (D b)) as [Hdb|Hdb].
        + left. by apply (lin_pre _ _ _ _ HR1).
        + auto.
        + by destruct Hda; apply (HDdown a b).
        + right; left. by apply (lin_pre _ _ _ _ HR2).
      - intros ia ib ra rb Ha Hb Hiab Hibra.
        destruct (classic (D ra)) as [Hdra|Hdra].
        + assert (Hdia : D ia) by (by apply (HDval ia ra)).
          assert (Hdib : D ib).
          { destruct Hibra as [Hibra|[Hibra|(_ & _ & ?)]]; [by destruct (Hdom1 _ _ Hibra)| |done].
            by destruct (Hdom2 _ _ Hibra) as [_ [_ ?]]. }
          left. eapply (lin_lifo _ _ _ _ HR1); [done|done| |].
          * destruct Hiab as [?|[Hiab|(_ & _ & ?)]]; [done| |done].
            by destruct (Hdom2 _ _ Hiab) as [[_ ?] _].
          * destruct Hibra as [?|[Hibra|(_ & _ & ?)]]; [done| |done].
            by destruct (Hdom2 _ _ Hibra) as [_ [_ ?]].
        + assert (Hdia : ¬ D ia) by (by rewrite (HDval ia ra)).
          assert (Hiab' : R2 ia ib).
          { destruct Hiab as [Hiab|[?|(? & _ & _)]]; [by destruct (Hdom1 _ _ Hiab)|done|done]. }
          assert (Hibra' : R2 ib ra).
          { destruct (Hdom2 _ _ Hiab') as [_ [_ Hdib]].
            destruct Hibra as [Hibra|[?|(? & _ & _)]]; [by destruct (Hdom1 _ _ Hibra)|done|done]. }
          right; left. by eapply (lin_lifo _ _ _ _ HR2).
    Qed.

    (* Wrapping: [x] is first and its pop [p] is last. *)
    Local Lemma lin_of_wrap (S : operation → Prop) x p R0 :
      val_closed val S → S x → S p → val x p →
      (∀ o, S o → ¬ pre o x) → (∀ o, S o → ¬ pre p o) →
      lin_of pre val (λ o, S o ∧ o ≠ x ∧ o ≠ p) R0 →
      lin_of pre val S (λ a b, R0 a b ∨ (a = x ∧ S b ∧ b ≠ x) ∨ (S a ∧ a ≠ p ∧ b = p)).
    Proof.
      intros HSval HSx HSp Hxp Hnpre_x Hnpre_p HR0.
      pose proof (lin_dom _ _ _ _ HR0) as Hdom.
      assert (Hxnp : x ≠ p) by (intros ->; exact (pre_irrefl _ (Hvp _ _ Hxp))).
      constructor.
      - intros a b [Hab|[(-> & Hb & _)|(Ha & _ & ->)]]; [by destruct (Hdom _ _ Hab) as [[] []]|done|done].
      - intros a [Haa|[(-> & _ & ?)|(_ & ? & ->)]]; [by eapply (lin_irrefl _ _ _ _ HR0)|done|done].
      - intros a b c [Hab|[(-> & Hb & Hbx)|(Ha & Hap & ->)]] [Hbc|[(-> & Hc & Hcx)|(Hb' & Hbp & ->)]].
        + left. by eapply lin_trans.
        + by destruct (Hdom _ _ Hab) as [_ (_ & ? & _)].
        + right; right. by destruct (Hdom _ _ Hab) as [(? & _ & ?) _].
        + right; left. by destruct (Hdom _ _ Hbc) as [_ (? & ? & _)].
        + done.
        + right; left. done.
        + by destruct (Hdom _ _ Hbc) as [(_ & _ & ?) _].
        + done.
        + done.
      - intros a b Ha Hb Hne.
        destruct (decide (a = x)) as [->|Hax].
        { left; right; left. split_and!; [done|done|by intros ->]. }
        destruct (decide (b = x)) as [->|Hbx]; first by right; right; left.
        destruct (decide (a = p)) as [->|Hap].
        { right; right; right. split_and!; [done|by intros ->|done]. }
        destruct (decide (b = p)) as [->|Hbp]; first by left; right; right.
        destruct (lin_total _ _ _ _ HR0 a b) as [|]; auto.
      - intros a b Ha Hb Hab.
        destruct (decide (a = x)) as [->|Hax].
        { right; left. split_and!; [done|done|]. intros ->. exact (pre_irrefl _ Hab). }
        destruct (decide (b = p)) as [->|Hbp].
        { right; right. split_and!; [done| |done]. intros ->. exact (pre_irrefl _ Hab). }
        destruct (decide (b = x)) as [->|Hbx]; first by destruct (Hnpre_x a).
        destruct (decide (a = p)) as [->|Hap]; first by destruct (Hnpre_p b).
        left. by apply (lin_pre _ _ _ _ HR0).
      - intros ia ib ra rb Ha Hb Hiab Hibra.
        assert (Hneq : ∀ o, (R0 o x → False) ∧ (R0 p o → False)).
        { intros o. split; intros Ho; destruct (Hdom _ _ Ho) as [? ?]; naive_solver. }
        destruct (decide (ra = p)) as [->|Hrap].
        { right; right. split_and!.
          - apply (HSval ib rb Hb).
            destruct Hibra as [Hibra|[(-> & _ & _)|(? & _ & _)]]; [|done|done].
            by destruct (Hdom _ _ Hibra) as [(? & _ & _) _].
          - intros ->. pose proof (def_push_once _ _ _ Ha Hb) as <-.
            destruct Hiab as [?|[(-> & _ & ?)|(_ & ? & ->)]]; [by eapply (lin_irrefl _ _ _ _ HR0)|done|done].
          - done. }
        assert (Hibx : ib ≠ x).
        { intros ->. destruct Hiab as [Hiab|[(-> & _ & ?)|(_ & _ & ->)]]; [|done|done].
          exact (proj1 (Hneq ia) Hiab). }
        assert (Hibra' : R0 ib ra).
        { destruct Hibra as [?|[(? & _ & _)|(_ & _ & ?)]]; done. }
        assert (Hiax : ia ≠ x).
        { intros ->. by apply Hrap, (def_pop_once _ _ _ Ha). }
        assert (Hiab' : R0 ia ib).
        { destruct Hiab as [?|[(? & _ & _)|(_ & _ & ->)]]; [done|done|].
          destruct (Hdom _ _ Hibra') as [(_ & _ & ?) _]. done. }
        left. by eapply (lin_lifo _ _ _ _ HR0).
    Qed.

    (* The closure of the precedence predecessors of [x] within [S]. *)
    Inductive clo (S : operation → Prop) (x : operation) : operation → Prop :=
    | clo_pre o : S o → pre o x → clo S x o
    | clo_push o r : clo S x o → val o r → clo S x r
    | clo_pop o r : clo S x r → val o r → clo S x o
    | clo_down w o : S w → pre w o → clo S x o → clo S x w.

    Section closure.
      Context (S : operation → Prop) (x p : operation).
      Hypotheses (HSop : ∀ o, S o → is_push val o ∨ is_pop val o) (HSval : val_closed val S)
        (Hxp : val x p) (HSp : S p)
        (Hmax : ∀ q, S q → is_pop val q → q ≠ p → rr q p).

      Local Lemma clo_S o : clo S x o → S o.
      Proof.
        induction 1 as [o|o r|o r|w o]; try done.
        - by apply (HSval o r).
        - by apply (HSval o r).
      Qed.

      (* Condition 2 together with the maximality of [p]: the pop of a push that is
         ts-before [x] is vis-before [x]. *)
      Local Lemma pop_before_x o r :
        S o → val o r → tc (pre ∪ vis) o x → ts_order pre vis o x → tc (pre ∪ vis) r x.
      Proof.
        intros Ho Hor Hox Hts.
        destruct (alternating_complete _ _ vis_rr_alternating x r) as [Hxr|Hrx];
          [by exists p|by exists o| |by apply tc_once; right].
        destruct (vis_rr_lifo o r x Hor (Hvp _ _ Hor) Hts Hxr) as (rb & Hxrb & Hrbr).
        rewrite (def_pop_once _ _ _ Hxrb Hxp) in Hrbr.
        assert (Hrp : r ≠ p).
        { intros ->. rewrite (def_push_once _ _ _ Hor Hxp) in Hox.
          by apply (vis_rr_pr_u_vis_acyclic x). }
        exfalso. eapply rr_asym; [exact Hrbr|]. apply Hmax; [by apply (HSval o r)|by exists o|done].
      Qed.

      Local Lemma clo_before o :
        clo S x o → tc (pre ∪ vis) o x ∧
          ∀ r, val o r → ts_order pre vis o x ∧ tc (pre ∪ vis) r x.
      Proof.
        induction 1 as [o Ho Hox|o r Hclo [IHo IHr] Hor|o r Hclo [IHo IHr] Hor|w o Hw Hwo Hclo [IHo IHr]].
        - assert (Hts : ts_order pre vis o x) by (left; done).
          assert (Hox' : tc (pre ∪ vis) o x) by (apply tc_once; left; done).
          split; first done. intros r Hor. split; first done. by eapply pop_before_x.
        - split; first by apply IHr.
          intros r' Hrr'. exfalso. eapply def_val_order; [exact Hor|]. exists r'. by right.
        - assert (Hrx : vis r x) by (apply vis_of_tc_pop_push; [by exists o|by exists p|done]).
          split; first (eapply tc_l; [left; by apply Hvp|done]).
          intros r' Hor'. rewrite (def_pop_once _ _ _ Hor' Hor). split; last done.
          right; left. exists r. split; [by apply Hvp|done].
        - assert (Hwx : tc (pre ∪ vis) w x) by (eapply tc_l; [left; exact Hwo|done]).
          assert (Hts : ts_order pre vis w x).
          { destruct (HSop o (clo_S o Hclo)) as [[r Hor]|Hop].
            - destruct (IHr r Hor) as [_ Hrx]. right; right. exists o, r. split_and!; [done| |].
              + apply vis_of_pre_push_pop; [by exists r|by exists o|by apply Hvp].
              + apply vis_of_tc_pop_push; [by exists o|by exists p|done].
            - right; left. exists o. split; first done.
              apply vis_of_tc_pop_push; [done|by exists p|done]. }
          split; first done. intros r Hwr. split; first done. by eapply pop_before_x.
      Qed.

      Local Lemma clo_not_x : ¬ clo S x x.
      Proof. intros Hclo. destruct (clo_before x Hclo) as [Hxx _]. by eapply vis_rr_pr_u_vis_acyclic. Qed.

      Local Lemma clo_not_p : ¬ clo S x p.
      Proof.
        intros Hclo. destruct (clo_before p Hclo) as [Hpx _].
        apply (vis_rr_pr_u_vis_acyclic x). eapply tc_l; [left; by apply Hvp|done].
      Qed.
    End closure.

    (* The rr-last pop has no precedence successor. *)
    Local Lemma rr_max_pre_max (S : operation → Prop) p :
      (∀ o, S o → is_push val o ∨ is_pop val o) → val_closed val S →
      (∀ q, S q → is_pop val q → q ≠ p → rr q p) → ∀ o, S o → ¬ pre p o.
    Proof.
      intros HSop HSval Hmax o Ho Hpo.
      assert (∃ q, S q ∧ is_pop val q ∧ pre p q) as (q & Hq & Hqp & Hpq).
      { destruct (HSop o Ho) as [[r Hor]|Hop].
        - exists r. split_and!; [by apply (HSval o r)|by exists o|by trans o; [|apply Hvp]].
        - by exists o. }
      assert (q ≠ p) by (intros ->; exact (pre_irrefl _ Hpq)).
      eapply rr_pre_asym; [exact Hpq|by apply Hmax].
    Qed.

    Local Lemma lin_exists n : ∀ (S : operation → Prop) (l : list operation),
      length l ≤ n → (∀ o, S o → o ∈ l) →
      (∀ o, S o → is_push val o ∨ is_pop val o) → val_closed val S → ∃ R, lin_of pre val S R.
    Proof.
      induction n as [|n IH]; intros S l Hlen Hl HSop HSval.
      { exists (λ _ _, False). apply lin_of_empty. intros o Ho.
        destruct l; [by apply (elem_of_nil o), Hl|simpl in Hlen; lia]. }
      destruct (classic (∃ q, S q ∧ is_pop val q)) as [Hne|Hnone].
      2:{ exists (λ _ _, False). apply lin_of_empty. intros o Ho. apply Hnone.
          destruct (HSop o Ho) as [[r Hor]|Hop]; last by exists o.
          exists r. split; [by apply (HSval o r)|by exists o]. }
      destruct (rr_max S l Hl Hne) as (p & HSp & [x Hxp] & Hmax).
      assert (HSx : S x) by (by apply (HSval x p)).
      (* Sub-histories are bounded by [l] without one of their absent elements. *)
      assert (Hsub : ∀ (S' : operation → Prop) y, S y → ¬ S' y → (∀ o, S' o → S o) →
        ∃ l', length l' ≤ n ∧ ∀ o, S' o → o ∈ l').
      { intros S' y Hy Hny HS'. exists (filter (λ o, o ≠ y) l). split.
        - pose proof (length_filter_lt (λ o, o ≠ y) l y (Hl y Hy) (λ Hn, Hn eq_refl)). lia.
        - intros o Ho. apply list_elem_of_filter. split; [by intros ->|by apply Hl, HS']. }
      destruct (classic (∃ o, clo S x o)) as [[o Ho]|Hnclo].
      - assert (HDS : ∀ o, clo S x o → S o) by (intros o'; by eapply clo_S).
        assert (HDval : val_closed val (clo S x)).
        { intros a b Hab. split; intros Hclo; [by eapply clo_push|by eapply clo_pop]. }
        destruct (Hsub (clo S x) x HSx (clo_not_x S x p HSop HSval Hxp Hmax) HDS)
          as (l1 & Hlen1 & Hl1).
        destruct (IH (clo S x) l1) as [R1 HR1]; [done|done|auto|done|].
        destruct (Hsub (λ o, S o ∧ ¬ clo S x o) o (HDS o Ho) (λ Hn, proj2 Hn Ho)
          (λ _ Ho', proj1 Ho')) as (l2 & Hlen2 & Hl2).
        destruct (IH (λ o, S o ∧ ¬ clo S x o) l2) as [R2 HR2]; [done|done|naive_solver| |].
        { intros a b Hab. rewrite (HSval a b Hab) (HDval a b Hab). done. }
        eexists. apply (lin_of_app S (clo S x) R1 R2 HDS HDval); [|done|done].
        intros a b Ha Hb Hab. by eapply clo_down.
      - assert (Hnpre_x : ∀ o, S o → ¬ pre o x).
        { intros o' Ho' Hpre. apply Hnclo. exists o'. by constructor. }
        assert (Hnpre_p : ∀ o, S o → ¬ pre p o) by (by apply rr_max_pre_max).
        assert (Hxnp : x ≠ p) by (intros ->; exact (pre_irrefl _ (Hvp _ _ Hxp))).
        destruct (Hsub (λ o, S o ∧ o ≠ x ∧ o ≠ p) x HSx (λ Hn, proj1 (proj2 Hn) eq_refl)
          (λ _ Ho', proj1 Ho')) as (l0 & Hlen0 & Hl0).
        destruct (IH (λ o, S o ∧ o ≠ x ∧ o ≠ p) l0) as [R0 HR0]; [done|done|naive_solver| |].
        { intros a b Hab. rewrite (HSval a b Hab). split.
          - intros (Hb & Hax & Hap). split_and!; [done| |].
            + intros ->. by eapply push_not_pop; [exists p|exists a].
            + intros ->. by apply Hax, (def_push_once _ _ _ Hab).
          - intros (Hb & Hbx & Hbp). split_and!; [done| |].
            + intros ->. by apply Hbp, (def_pop_once _ _ _ Hab).
            + intros ->. by eapply push_not_pop; [exists b|exists x]. }
        eexists. exact (lin_of_wrap S x p R0 HSval HSx HSp Hxp Hnpre_x Hnpre_p HR0).
    Qed.

    (* Lemma 3 on elimination-free histories, as a linearization. *)
    Lemma vis_rr_sequential_stack : ∃ prt, subrelation pre prt ∧ SequentialStack prt val.
    Proof.
      destruct (operation_finite) as (enum & _ & Henum).
      destruct (lin_exists (length enum) (λ o, is_push val o ∨ is_pop val o) enum)
        as [R HR]; [done|done|done| |].
      { intros a b Hab. pose proof (val_push_pop a b Hab). naive_solver. }
      assert (Hop : ∀ a, (∃ c, val a c ∨ val c a) → is_push val a ∨ is_pop val a).
      { intros a (c & [Hac|Hca]); [left|right]; by eexists. }
      assert (Hsub : subrelation pre R).
      { intros a b Hab. destruct (def_push_or_pop a b Hab).
        apply (lin_pre _ _ _ _ HR); auto. }
      exists R. split; first done.
      split; [split; [split| | |]|].
      - intros a b c. by apply (lin_trans _ _ _ _ HR).
      - intros a b Hab Hba. exfalso.
        exact (lin_irrefl _ _ _ _ HR a (lin_trans _ _ _ _ HR a b a Hab Hba)).
      - intros a. by apply (lin_irrefl _ _ _ _ HR).
      - apply operation_finite.
      - apply def_push_once.
      - apply def_pop_once.
      - apply def_val_order.
      - intros a b Hab. destruct (lin_dom _ _ _ _ HR a b Hab) as [[[c ?]|[c ?]] [[d ?]|[d ?]]];
          split; eauto.
      - intros ia ra Hval Hria. apply (lin_irrefl _ _ _ _ HR ia).
        eapply (lin_trans _ _ _ _ HR); [apply Hsub, Hvp, Hval|exact Hria].
      - intros a b Ha Hb Hne. apply (lin_total _ _ _ _ HR); auto.
      - intros a b Ha Hb Hne. apply (lin_total _ _ _ _ HR); auto.
      - intros a b Ha Hb.
        assert (a ≠ b) by (intros ->; by eapply push_not_pop).
        apply (lin_total _ _ _ _ HR); auto.
      - apply (lin_lifo _ _ _ _ HR).
    Qed.
  End lemma3.

  Lemma elim_free_val_pre pre val a b :
    WellformedHistory pre val → elim_free_val pre val a b → pre a b.
  Proof.
    intros Hwf (_ & (d & Hsv & Hpre) & Hab). destruct Hsv as [Hbd|Hdb].
    - exfalso. eapply def_val_order; [exact Hab|]. exists d. by right.
    - rewrite (def_push_once _ _ _ Hdb Hab) in Hpre. destruct Hpre as [Hba|]; last done.
      exfalso. by eapply def_val_then_not_pr.
  Qed.

  (* The premises restricted to the elimination-free sub-history. *)
  Lemma vis_rr_elim_free pre val vis rr :
    WellformedHistory pre val → VisRr pre val vis rr →
    VisRr (elim_free_pre pre val) (elim_free_val pre val)
          (elim_free_ir pre val vis) (elim_free_ir pre val rr).
  Proof.
    intros Hwf Hvr.
    assert (Hpop : ∀ a, is_pop (elim_free_val pre val) a → elim_free pre val a ∧ is_pop val a).
    { intros a [b (_ & Hefa & Hba)]. split; [done|by exists b]. }
    assert (Hsub : ∀ R, subrelation (elim_free_pre pre val ∪ elim_free_ir pre val R) (pre ∪ R)).
    { intros R a b [(_ & _ & Hab)|(_ & _ & Hab)]; [by left|by right]. }
    constructor.
    - apply alternating_then_ef_alternating; [done|apply vis_rr_alternating].
    - intros a Haa. apply (vis_rr_pr_u_vis_acyclic a). by eapply tc_subrel; [apply Hsub|].
    - intros a b Ha Hb Hne. apply Hpop in Ha as [Hefa Ha], Hb as [Hefb Hb].
      destruct (vis_rr_total a b Ha Hb Hne); [left|right]; by split_and!.
    - intros a Haa. apply (vis_rr_pr_u_rr_acyclic a). by eapply tc_subrel; [apply Hsub|].
    - intros ia ra ib (Hefia & Hefra & Hval) (_ & _ & Hpre) Hts (Hefib & _ & Hvis).
      destruct (vis_rr_lifo ia ra ib Hval) as (rb & Hrb & Hrr).
      + done.
      + destruct Hts as [(_ & _ & ?)|[(c & (_ & _ & ?) & (_ & _ & ?))|
                                      (d & c & (_ & _ & ?) & (_ & _ & ?) & (_ & _ & ?))]];
          [by left|right; left; by exists c|right; right; by exists d, c].
      + done.
      + exists rb. pose proof (val_then_ef_val pre val ib rb Hefib Hrb def_val_order def_pop_once)
          as Hefrb.
        split; first done. destruct Hefrb as (_ & ? & _). by split_and!.
  Qed.

  (* Theorem 1 with order-correctness replaced by the premises of Lemma 3. *)
  Theorem abstract_stack_theorem_vis pre val empty vis rr :
    linearizable_set pre val empty → VisRr (non_empty_pre pre empty) val vis rr →
    linearizable_stack pre val empty.
  Proof.
    intros Hls Hvr.
    assert (Hch : ConcHistory pre) by (by destruct Hls as [Hch _]).
    assert (Hch_ne : ConcHistory (non_empty_pre pre empty)).
    { by apply pre_conc_history_then_non_empty_pre_conc_history. }
    assert (Hwf_ne : WellformedHistory (non_empty_pre pre empty) val).
    { by apply linearizable_set_then_wellformed. }
    assert (Hlin_ef : linearizable_non_empty_stack
                        (elim_free_pre (non_empty_pre pre empty) val)
                        (elim_free_val (non_empty_pre pre empty) val)).
    { split; first by apply ef_conf_history.
      assert (WellformedHistory (elim_free_pre (non_empty_pre pre empty) val)
                                (elim_free_val (non_empty_pre pre empty) val)).
      { by apply wellformed_then_ef_wellformed. }
      assert (VisRr (elim_free_pre (non_empty_pre pre empty) val)
                    (elim_free_val (non_empty_pre pre empty) val)
                    (elim_free_ir (non_empty_pre pre empty) val vis)
                    (elim_free_ir (non_empty_pre pre empty) val rr)).
      { by apply vis_rr_elim_free. }
      apply (vis_rr_sequential_stack _ _
               (elim_free_ir (non_empty_pre pre empty) val vis)
               (elim_free_ir (non_empty_pre pre empty) val rr)).
      intros a b Hab. split_and!; [by destruct Hab as (? & _)|by destruct Hab as (_ & ? & _)|].
      by apply (elim_free_val_pre _ val). }
    assert (Hlin_ne : linearizable_non_empty_stack (non_empty_pre pre empty) val).
    { apply elimination_theorem; [done|apply Hch_ne|done]. }
    by apply concurrent_empty_stack_linearizable_main.
  Qed.
End vis_rr.
