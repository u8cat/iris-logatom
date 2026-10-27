(* remove_relaxed_stack.v, ported from remove_relaxed_stack.thy *)

From stdpp Require Import finite.
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect.bag.ext Require Import strict_partial_order_extension.
From iris_logatom.pure_logic.aspect.stack.ext Require Import conc_his_rel insert_relaxed_stack insert_pr_relaxed_stack.

Local Instance relation_union {A} : Union (relation A) :=
  λ r1 r2, Relation_Operators.union A r1 r2.

Section remove_relaxed_stack.
  Context `{abstract_stack_model}.
  Implicit Types (pre val : relation operation).

  (* remove_relaxed_stack.thy:5-13 *)
  Class RemoveRelaxedStack pre val ir := {
    #[local] rrs_wellformed :: WellformedHistory pre val;
    #[local] rrs_abcd :: Abcd pre;
    rrs_val_then_pr ia ra : val ia ra → pre ia ra;
    rrs_ir_alternating : alternating val ir;
    rrs_pr_u_ir_acyclic : Acyclic (pre ∪ ir);
    rrs_rem_ooo ia ra ib rb : val ia ra → val ib rb → ins_order pre val ir ia ib →
      ir ib ra → ¬ rem_order pre val ir ra rb;
    rrs_pops_finite : FinitePredicate (λ a, is_pop val a);
  }.

  (* remove_relaxed_stack.thy:15-34 *)
  Lemma remove_relaxed_stackI pre val ir :
    WellformedHistory pre val →
    Abcd pre →
    (∀ a b, val a b → pre a b) →
    alternating val ir →
    Acyclic (pre ∪ ir) →
    (∀ ia ra ib rb, val ia ra → val ib rb → ins_order pre val ir ia ib →
      ir ib ra → ¬ rem_order pre val ir ra rb) →
    FinitePredicate (λ a, is_pop val a) →
    RemoveRelaxedStack pre val ir.
  Proof.
    intros Hwf Habcd Hvp Halt Hacyc Hrem Hfin.
    constructor; done.
  Qed.

  (* remove_relaxed_stack.thy:36-45 *)
  Lemma remove_relaxed_stackD pre val ir :
    RemoveRelaxedStack pre val ir →
    WellformedHistory pre val ∧ Abcd pre ∧
    (∀ a b, val a b → pre a b) ∧
    alternating val ir ∧
    Acyclic (pre ∪ ir) ∧
    (∀ ia ra ib rb, val ia ra → val ib rb → ins_order pre val ir ia ib →
      ir ib ra → ¬ rem_order pre val ir ra rb).
  Proof.
    intros Hrrs.
    destruct Hrrs as [Hwf Habcd Hvtp Halt Hacyclic Hrem Hfin].
    split; [done|].
    split; [done|].
    split; [apply Hvtp|].
    split; [done|].
    split; [done|].
    apply Hrem.
  Qed.

  (* remove_relaxed_stack.thy:47-109 *)
  Lemma order_correct_then_remove_relaxed_stack pre val empty
      `{!RelDecision pre, !RelDecision val, ∀ a, Decision (empty a)} :
    linearizable_set pre val empty →
    order_correct pre val →
    ∃ ir' (_ : RelDecision ir'), RemoveRelaxedStack
      (elim_free_pre (non_empty_pre pre empty) val)
      (elim_free_val (non_empty_pre pre empty) val)
      (elim_free_ir (non_empty_pre pre empty) val ir').
  Proof.
    intros Hls Hoc.
    (* Extract ir from order_correct *)
    destruct Hoc as (ir & Hir_dec & Halt & Hacyc & Hooo).
    exists ir, Hir_dec.
    (* Get helper facts *)
    assert (Hwf_ne : WellformedHistory (non_empty_pre pre empty) val).
    { by apply linearizable_set_then_wellformed. }
    assert (Hwf_ef : WellformedHistory (elim_free_pre (non_empty_pre pre empty) val)
                                        (elim_free_val (non_empty_pre pre empty) val)).
    { by apply wellformed_then_ef_wellformed. }
    assert (Hch : ConcHistory pre).
    { by destruct Hls as [Hch _]. }
    assert (Hch_ne : ConcHistory (non_empty_pre pre empty)).
    { by apply pre_conc_history_then_non_empty_pre_conc_history. }
    assert (Hch_ef : ConcHistory (elim_free_pre (non_empty_pre pre empty) val)).
    { by apply ef_conf_history. }
    (* Apply remove_relaxed_stackI *)
    apply remove_relaxed_stackI.
    - (* WellformedHistory *)
      exact Hwf_ef.
    - (* Abcd *)
      apply Hch_ef.
    - (* val_then_pre *)
      intros a b Hval.
      destruct Hval as (Hefa & Hefb & Hvab).
      split; last split.
      + exact Hefa.
      + exact Hefb.
      + (* Show (non_empty_pre pre empty) a b *)
        split; last split.
        * eapply ef_val_then_pre; [exact Hwf_ne|].
          split; last split; done.
        * (* ¬empty a from Hefa *)
          destruct Hefa as (c & Hsv & Hpre).
          destruct Hpre as [(Hpreac & Hnea & Hnec)|(Hpreca & Hnec & Hnea)]; done.
        * (* ¬empty b from Hefb *)
          destruct Hefb as (c & Hsv & Hpre).
          destruct Hpre as [(Hprebc & Hneb & Hnec)|(Hprecb & Hnec & Hneb)]; done.
    - (* alternating *)
      apply alternating_then_ef_alternating; done.
    - (* Acyclic *)
      eapply acyclic_subset; last exact Hacyc.
      (* Need: subrelation (elim_free_pre ... ∪ elim_free_ir ...) (pre ∪ ir) *)
      intros a b [Hefpre|Hefir].
      + (* elim_free_pre case *)
        left. eapply ef_empty_mono; [|exact Hefpre].
        intros x y Hxy. exact Hxy.
      + (* elim_free_ir case *)
        right. eapply ef_ir_in_ir. exact Hefir.
    - (* ooo condition *)
      intros ia ra ib rb Hvalia Hvalib Hinsord Hibirra Hrem.
      (* Translate to original relations and use Hooo *)
      assert (Hvalia' : val ia ra) by (eapply ef_val_then_val; exact Hvalia).
      assert (Hvalib' : val ib rb) by (eapply ef_val_then_val; exact Hvalib).
      assert (Hpreiara : pre ia ra) by (eapply ef_val_then_pre; [exact Hwf_ne|exact Hvalia]).
      (* Need to show ins_order pre val ir ia ib from ins_order ef_pre ef_val ef_ir ia ib *)
      destruct Hinsord as (Hpushia & Hpushib & Hord).
      assert (Hinsord' : ins_order pre val ir ia ib).
      { split; last split.
        - (* is_push val ia *)
          destruct Hpushia as [c (Hefa & Hefc & Hiac)].
          exists c. done.
        - (* is_push val ib *)
          destruct Hpushib as [c (Hefb & Hefc & Hibc)].
          exists c. done.
        - (* pre ia ib or ∃c, pre ia c ∧ ir c ib *)
          destruct Hord as [(Hefia & Hefib & (Hpre & _ & _))|(c & (Hefia & Hefc & (Hpreiac & _ & _)) & (Hefc' & Hefib & Hircib))].
          + left. done.
          + right. exists c. done. }
      (* ir ib ra from ef_ir *)
      assert (Hibirra' : ir ib ra).
      { destruct Hibirra as (Hefib & Hefra & Hir). done. }
      (* Apply Hooo *)
      destruct (Hooo ia ra ib Hvalia' Hpreiara Hinsord' Hibirra') as [rb' [Hvalib'' Hnrem]].
      (* Derive rem_order pre val ir ra rb from rem_order ef versions *)
      assert (Hrem_ne : rem_order (non_empty_pre pre empty) val ir ra rb).
      { eapply elim_ef_rem_then_rem; [exact Hrem|exact Hwf_ne]. }
      assert (Hrem' : rem_order pre val ir ra rb).
      { eapply empty_rem_then_rem; [exact Hrem_ne|exact Hwf_ne]. }
      (* Get rb' = rb from pop_once *)
      assert (Hrbeq : rb' = rb).
      { eapply (@def_pop_once _ _ _ Hwf_ne); [exact Hvalib''|exact Hvalib']. }
      subst rb'.
      by apply Hnrem.
    - (* FinitePredicate for pops *)
      destruct Hwf_ef as [_ _ _ Hfin _ _ _ _ _].
      destruct Hfin as [enum [Hnodup Henum]].
      exists enum. split; first done.
      intros x Hpopx.
      apply Henum. right. done.
  Qed.

  Context pre val ir `{!RemoveRelaxedStack pre val ir}.
  Context `{!RelDecision pre, !RelDecision val, !RelDecision ir}.

  (* Make parent class instances available *)
  #[local] Existing Instance rrs_wellformed.
  #[local] Existing Instance rrs_abcd.
  #[local] Existing Instance wf_pre_transitive.
  #[local] Existing Instance wf_pre_antisymmetric.
  #[local] Existing Instance wf_pre_irreflexive.

  (* remove_relaxed_stack.thy:114-115 *)
  Lemma rrs_pops_finite' : FinitePredicate (λ a, is_pop val a).
  Proof. apply rrs_pops_finite. Qed.

  (* remove_relaxed_stack.thy:117-118 *)
  Lemma push_pop_ordered a b : is_push val a → is_pop val b → ir a b ∨ ir b a.
  Proof.
    intros Hpush Hpop.
    apply (alternating_complete _ _ rrs_ir_alternating); done.
  Qed.

  (* remove_relaxed_stack.thy:120-121 *)
  Lemma ir_push_and_pop a b : ir a b → (is_push val a ∧ is_pop val b) ∨ (is_pop val a ∧ is_push val b).
  Proof.
    intros Hir.
    apply (alternating_sound _ _ rrs_ir_alternating). done.
  Qed.

  (* remove_relaxed_stack.thy:123-125 *)
  Definition ins : relation operation := ins_order pre val ir.

  (* remove_relaxed_stack.thy:127-131 *)
  Lemma lem_pr_then_ins a b : is_push val a → is_push val b → pre a b → ins a b.
  Proof.
    intros Hpusha Hpushb Hpre.
    unfold ins, ins_order.
    split; [done|]. split; [done|]. left. done.
  Qed.

  (* remove_relaxed_stack.thy:133-134 *)
  Lemma ir_push_and_pop1 a b : ir a b → is_push val a → is_pop val b.
  Proof.
    intros Hir [ra Hval].
    destruct (ir_push_and_pop _ _ Hir) as [[_ Hpopb]|[Hpopa _]].
    - done.
    - exfalso. destruct Hpopa as [c Hca].
      eapply def_val_order; first exact Hval.
      exists c. left. done.
  Qed.

  (* remove_relaxed_stack.thy:136-137 *)
  Lemma ir_push_and_pop2 a b : ir a b → is_push val b → is_pop val a.
  Proof.
    intros Hir [rb Hval].
    destruct (ir_push_and_pop _ _ Hir) as [[_ Hpopb]|[Hpopa _]].
    - exfalso. destruct Hpopb as [c Hcb].
      eapply def_val_order; first exact Hval.
      exists c. left. done.
    - done.
  Qed.

  (* remove_relaxed_stack.thy:139-140 *)
  Lemma ir_push_and_pop3 a b : ir a b → is_pop val a → is_push val b.
  Proof.
    intros Hir [c Hca].
    destruct (ir_push_and_pop _ _ Hir) as [[Hpusha _]|[_ Hpushb]].
    - exfalso. destruct Hpusha as [ra Hara].
      eapply def_val_order; first exact Hara.
      exists c. left. done.
    - done.
  Qed.

  (* remove_relaxed_stack.thy:142-143 *)
  Lemma ir_push_and_pop4 a b : ir a b → is_pop val b → is_push val a.
  Proof.
    intros Hir [c Hcb].
    destruct (ir_push_and_pop _ _ Hir) as [[Hpusha _]|[_ Hpushb]].
    - done.
    - exfalso. destruct Hpushb as [rb Hbrb].
      eapply def_val_order; first exact Hbrb.
      exists c. left. done.
  Qed.

  (* remove_relaxed_stack.thy:145-146 *)
  Lemma insI a b c : is_push val a → is_push val b → pre a c → ir c b → ins a b.
  Proof.
    intros Hpusha Hpushb Hpre Hir.
    unfold ins, ins_order.
    split; [done|]. split; [done|]. right. exists c. done.
  Qed.

  (* remove_relaxed_stack.thy:148-149 *)
  Lemma insD a b : ins a b → is_push val a ∧ is_push val b ∧
    (pre a b ∨ ∃ c, is_pop val c ∧ pre a c ∧ ir c b).
  Proof.
    intros (Hpusha & Hpushb & Horder).
    split; [done|]. split; [done|].
    destruct Horder as [Hpre|(c & Hpre & Hir)].
    - left. done.
    - right. exists c. split; [|done].
      apply (ir_push_and_pop2 _ _ Hir). done.
  Qed.

  (* remove_relaxed_stack.thy:151-155 *)
  Lemma ipr_ooo ia ra ib rb : val ia ra → val ib rb → ins_order pre val ir ia ib →
    ir ib ra → ¬ pre ra rb.
  Proof.
    intros Hvala Hvalb Hins Hir Hpre.
    assert (Hpopra : is_pop val ra) by (exists ia; done).
    assert (Hpoprb : is_pop val rb) by (exists ib; done).
    assert (Hpushib : is_push val ib) by (exists rb; done).
    assert (Hpushia : is_push val ia) by (exists ra; done).
    assert (Hrem : rem_order pre val ir ra rb).
    { unfold rem_order. split; [done|]. split; [done|]. left. done. }
    eapply rrs_rem_ooo; [exact Hvala | exact Hvalb | exact Hins | exact Hir | exact Hrem].
  Qed.

  (* remove_relaxed_stack.thy:157-161 *)
  Lemma ipr_ooo_ir ia ra ib rb ic : val ia ra → val ib rb → ins_order pre val ir ia ib →
    ir ib ra → ¬ (ir ra ic ∧ ir ic rb).
  Proof.
    intros Hvala Hvalb Hins Hir (Hraic & Hicrb).
    assert (Hpopra : is_pop val ra) by (exists ia; done).
    assert (Hpoprb : is_pop val rb) by (exists ib; done).
    assert (Hrem : rem_order pre val ir ra rb).
    { unfold rem_order. split; [done|]. split; [done|]. right. exists ic. done. }
    eapply rrs_rem_ooo; [exact Hvala | exact Hvalb | exact Hins | exact Hir | exact Hrem].
  Qed.

  (* remove_relaxed_stack.thy:163-175 *)
  Lemma lem_val_then_ir a b : val a b → ir a b.
  Proof.
    intros Hval.
    assert (Hpre : pre a b) by (by apply rrs_val_then_pr).
    assert (Hpusha : is_push val a) by (exists b; done).
    assert (Hpopb : is_pop val b) by (exists a; done).
    destruct (push_pop_ordered _ _ Hpusha Hpopb) as [Hir|Hirba].
    - done.
    - exfalso.
      assert (Htc_ba : tc (pre ∪ ir) b a) by (apply tc_once; right; done).
      assert (Htc_aa : tc (pre ∪ ir) a a) by (eapply tc_l; [left; exact Hpre|exact Htc_ba]).
      eapply rrs_pr_u_ir_acyclic. exact Htc_aa.
  Qed.

  (* remove_relaxed_stack.thy:177-186 *)
  Lemma lem_push_pr_pop_then_ir a b : is_push val a → is_pop val b → pre a b → ir a b.
  Proof.
    intros Hpusha Hpopb Hpre.
    destruct (push_pop_ordered _ _ Hpusha Hpopb) as [Hir|Hirba].
    - done.
    - exfalso.
      assert (Htc_ba : tc (pre ∪ ir) b a) by (apply tc_once; right; done).
      assert (Htc_aa : tc (pre ∪ ir) a a) by (eapply tc_l; [left; exact Hpre|exact Htc_ba]).
      eapply rrs_pr_u_ir_acyclic. exact Htc_aa.
  Qed.

  (* remove_relaxed_stack.thy:188-189 *)
  Lemma not_ir_push_pop_ir a b : ¬ ir a b → is_push val a → is_pop val b → ir b a.
  Proof.
    intros Hnir Hpusha Hpopb.
    destruct (push_pop_ordered _ _ Hpusha Hpopb) as [Hir|Hirba]; [done|done].
  Qed.

  (* remove_relaxed_stack.thy:191-192 *)
  Lemma not_ir_pop_push_ir a b : ¬ ir a b → is_pop val a → is_push val b → ir b a.
  Proof.
    intros Hnir Hpopa Hpushb.
    destruct (push_pop_ordered _ _ Hpushb Hpopa) as [Hir|Hirba]; [done|done].
  Qed.

  (* remove_relaxed_stack.thy:194-224 *)
  Lemma ir_transitive a b c d : ir a b → ir b c → ir c d → ir a d.
  Proof.
    intros Hab Hbc Hcd.
    destruct (decide (ir a d)) as [Had|Hnad]; [done|].
    destruct (ir_push_and_pop _ _ Hab) as [[Hpusha Hpopb]|[Hpopa Hpushb]].
    - (* a is push, b is pop *)
      assert (Hpushc : is_push val c) by (by apply (ir_push_and_pop3 _ _ Hbc)).
      assert (Hpopd : is_pop val d) by (by apply (ir_push_and_pop1 _ _ Hcd)).
      assert (Hda : ir d a) by (by apply not_ir_push_pop_ir).
      exfalso.
      assert (Htc : tc (pre ∪ ir) a a).
      { eapply tc_l; [right; exact Hab|].
        eapply tc_l; [right; exact Hbc|].
        eapply tc_l; [right; exact Hcd|].
        apply tc_once. right. exact Hda. }
      eapply rrs_pr_u_ir_acyclic. exact Htc.
    - (* a is pop, b is push *)
      assert (Hpopc : is_pop val c) by (by apply (ir_push_and_pop1 _ _ Hbc)).
      assert (Hpushd : is_push val d) by (by apply (ir_push_and_pop3 _ _ Hcd)).
      assert (Hda : ir d a) by (by apply not_ir_pop_push_ir).
      exfalso.
      assert (Htc : tc (pre ∪ ir) a a).
      { eapply tc_l; [right; exact Hab|].
        eapply tc_l; [right; exact Hbc|].
        eapply tc_l; [right; exact Hcd|].
        apply tc_once. right. exact Hda. }
      eapply rrs_pr_u_ir_acyclic. exact Htc.
  Qed.

  (* remove_relaxed_stack.thy:226-234 *)
  Lemma lem_pop_pr_push_then_ir a b : is_pop val a → is_push val b → pre a b → ir a b.
  Proof.
    intros Hpopa Hpushb Hpre.
    destruct (push_pop_ordered _ _ Hpushb Hpopa) as [Hirba|Hir].
    - exfalso.
      assert (Htc_ba : tc (pre ∪ ir) b a) by (apply tc_once; right; done).
      assert (Htc_aa : tc (pre ∪ ir) a a) by (eapply tc_l; [left; exact Hpre|exact Htc_ba]).
      eapply rrs_pr_u_ir_acyclic. exact Htc_aa.
    - done.
  Qed.

  (* remove_relaxed_stack.thy:236-245 *)
  Lemma lem_ins_transitive : Transitive ins.
  Proof.
    intros a b c Hab Hbc.
    destruct (insD _ _ Hab) as (Hpusha & Hpushb & Hordab).
    destruct (insD _ _ Hbc) as (Hpushb' & Hpushc & Hordbc).
    destruct Hordab as [Hprab|(d & Hpopd & Hprad & Hirdb)].
    - destruct Hordbc as [Hprbc|(e & Hpope & Hprbe & Hirec)].
      + apply lem_pr_then_ins; try done. by etrans.
      + apply (insI _ _ e); try done. by etrans.
    - destruct Hordbc as [Hprbc|(e & Hpope & Hprbe & Hirec)].
      + (* need abcd here *)
        destruct (abcd a d b c Hprad Hprbc) as [Hprac|Hprbd].
        * apply lem_pr_then_ins; done.
        * (* pre b d with b push, d pop gives ir b d, but we have ir d b, contradiction *)
          exfalso.
          assert (Hirbd : ir b d) by (apply lem_push_pr_pop_then_ir; done).
          assert (Htc : tc (pre ∪ ir) d d).
          { eapply tc_l; [right; exact Hirdb|].
            apply tc_once. right. exact Hirbd. }
          eapply rrs_pr_u_ir_acyclic. exact Htc.
      + (* We have pre a d, ir d b, pre b e, ir e c *)
        (* We need ins a c, i.e., pre a ? and ir ? c *)
        (* Use insI a c d with pre a d and ir d c *)
        (* ir d c: ir d b, need ir b ? and ir ? c *)
        (* Actually, we need ir d c. We have ir d b and ir e c. *)
        (* From ir d b: d is pop, b is push. From ir e c: e is pop, c is push. *)
        (* We have pre b e with b push, e pop, so ir b e. *)
        (* Then ir d b, ir b e, ir e c gives ir d c by ir_transitive. *)
        assert (Hirbe : ir b e) by (apply lem_push_pr_pop_then_ir; done).
        assert (Hirdc : ir d c) by (apply (ir_transitive d b e c); done).
        apply (insI _ _ d); done.
  Qed.

  (* remove_relaxed_stack.thy:247-254 *)
  Lemma lem_ins_abcd : Abcd ins.
  Proof.
    intros a b c d Hab Hcd.
    destruct (insD _ _ Hab) as (Hpusha & Hpushb & Hordab).
    destruct (insD _ _ Hcd) as (Hpushc & Hpushd & Hordcd).
    destruct Hordab as [Hprab|(e & Hpope & Hprae & Hireb)].
    - destruct Hordcd as [Hprcd|(f & Hpopf & Hprcf & Hirfd)].
      + destruct (abcd a b c d Hprab Hprcd) as [Hprad|Hprcb].
        * left. apply lem_pr_then_ins; done.
        * right. apply lem_pr_then_ins; done.
      + destruct (abcd a b c f Hprab Hprcf) as [Hpraf|Hprcb].
        * left. apply (insI _ _ f); done.
        * right. apply lem_pr_then_ins; done.
    - destruct Hordcd as [Hprcd|(f & Hpopf & Hprcf & Hirfd)].
      + destruct (abcd a e c d Hprae Hprcd) as [Hprad|Hprce].
        * left. apply lem_pr_then_ins; done.
        * right. apply (insI _ _ e); done.
      + destruct (abcd a e c f Hprae Hprcf) as [Hpraf|Hprce].
        * left. apply (insI _ _ f); done.
        * right. apply (insI _ _ e); done.
  Qed.

  (* remove_relaxed_stack.thy:256-271 *)
  Lemma lem_ins_irreflexive : Irreflexive ins.
  Proof.
    intros x Hxx.
    destruct (insD _ _ Hxx) as (Hpushx & _ & Hord).
    destruct Hord as [Hprxx|(c & Hpopc & Hprxc & Hircx)].
    - by eapply wf_pre_irreflexive.
    - assert (Htc : tc (pre ∪ ir) x x).
      { eapply tc_l; [left; exact Hprxc|].
        apply tc_once. right. done. }
      eapply rrs_pr_u_ir_acyclic. exact Htc.
  Qed.

  (* remove_relaxed_stack.thy:274-276 *)
  Definition lin : relation operation :=
    λ ra rb, ∃ ia ib, val ia ra ∧ val ib rb ∧ ins ib ia ∧ ir ia rb.

  (* remove_relaxed_stack.thy:278-280 *)
  Lemma linD ra rb : lin ra rb →
    ∃ ia ib, val ia ra ∧ val ib rb ∧ ins ib ia ∧ ir ia rb.
  Proof. done. Qed.

  (* remove_relaxed_stack.thy:282-292 *)
  Lemma linI ia ra ib rb : val ia ra → val ib rb → ir ia rb → ins ib ia → lin ra rb.
  Proof.
    intros Hvala Hvalb Hir Hins.
    exists ia, ib. done.
  Qed.

  (* remove_relaxed_stack.thy:294-296 *)
  Definition pop_ir : relation operation :=
    λ ra rb, is_pop val ra ∧ is_pop val rb ∧ (∃ ic, ir ra ic ∧ ir ic rb).

  (* remove_relaxed_stack.thy:298-300 *)
  Lemma pop_irD a b : pop_ir a b →
    is_pop val a ∧ is_pop val b ∧ (∃ ic, ir a ic ∧ ir ic b).
  Proof. done. Qed.

  (* remove_relaxed_stack.thy:302-305 *)
  Lemma pop_irI a b c : is_pop val a → is_pop val b → ir a c → ir c b → pop_ir a b.
  Proof.
    intros Hpopa Hpopb Hirac Hircb.
    split; [done|]. split; [done|]. exists c. done.
  Qed.

  (* remove_relaxed_stack.thy:307-326 *)
  Lemma lem_pop_ir_transitive : Transitive pop_ir.
  Proof.
    intros x y z Hxy Hyz.
    destruct (pop_irD _ _ Hxy) as (Hpopx & Hpopy & (icx & Hxicx & Hicxy)).
    destruct (pop_irD _ _ Hyz) as (Hpopy' & Hpopz & (icy & Hyicy & Hicyz)).
    destruct (decide (ir x icy)) as [Hxicy|Hnxicy].
    - apply (pop_irI _ _ icy); done.
    - (* ir icy x *)
      assert (Hpushicx : is_push val icx) by (by apply (ir_push_and_pop3 _ _ Hxicx)).
      assert (Hpushicy : is_push val icy) by (by apply (ir_push_and_pop3 _ _ Hyicy)).
      assert (Hicyx : ir icy x) by (by apply not_ir_pop_push_ir).
      exfalso.
      assert (Htc : tc (pre ∪ ir) x x).
      { eapply tc_l; [right; exact Hxicx|].
        eapply tc_l; [right; exact Hicxy|].
        eapply tc_l; [right; exact Hyicy|].
        apply tc_once. right. exact Hicyx. }
      eapply rrs_pr_u_ir_acyclic. exact Htc.
  Qed.

  (* remove_relaxed_stack.thy:328-341 *)
  Lemma lem_pop_ir_irreflexive : Irreflexive pop_ir.
  Proof.
    intros x Hxx.
    destruct (pop_irD _ _ Hxx) as (Hpopx & _ & (ic & Hxic & Hicx)).
    assert (Htc : tc (pre ∪ ir) x x).
    { eapply tc_l; [right; exact Hxic|].
      apply tc_once. right. exact Hicx. }
    eapply rrs_pr_u_ir_acyclic. exact Htc.
  Qed.

  (* remove_relaxed_stack.thy:343-349 *)
  Lemma lem_pop_ir_abcd : Abcd pop_ir.
  Proof.
    intros a b c d Hab Hcd.
    destruct (pop_irD _ _ Hab) as (Hpopa & Hpopb & (icab & Haicab & Hicabb)).
    destruct (pop_irD _ _ Hcd) as (Hpopc & Hpopd & (iccd & Hciccd & Hiccdd)).
    assert (Hpushicab : is_push val icab) by (by apply (ir_push_and_pop3 _ _ Haicab)).
    assert (Hpushiccd : is_push val iccd) by (by apply (ir_push_and_pop3 _ _ Hciccd)).
    destruct (push_pop_ordered _ _ Hpushicab Hpopd) as [Hicabd|Hdicab].
    - left. apply (pop_irI _ _ icab); done.
    - destruct (push_pop_ordered _ _ Hpushiccd Hpopb) as [Hiccdb|Hbiccd].
      + right. apply (pop_irI _ _ iccd); done.
      + (* Both Hdicab : ir d icab and Hbiccd : ir b iccd *)
        (* We have ir a icab, ir icab b, ir c iccd, ir iccd d *)
        (* and ir d icab, ir b iccd *)
        (* ir a icab, ir icab b, ir b iccd gives ir a iccd by ir_transitive *)
        left.
        assert (Haiccd : ir a iccd) by (apply (ir_transitive a icab b iccd); done).
        apply (pop_irI _ _ iccd); done.
  Qed.

  (* remove_relaxed_stack.thy:351-361 *)
  Lemma lem_lin_irreflexive : Irreflexive lin.
  Proof.
    intros x (ia & ib & Hvala & Hvalb & Hins & Hir).
    assert (Heq : ia = ib) by (eapply def_push_once; [exact Hvala | exact Hvalb]).
    subst ib.
    eapply lem_ins_irreflexive. exact Hins.
  Qed.

  (* remove_relaxed_stack.thy:363-378 *)
  Lemma lem_lin_transitive : Transitive lin.
  Proof.
    intros rc rb ra Hcb Hba.
    destruct (linD _ _ Hcb) as (ic & ib1 & Hvalc & Hvalb1 & Hinsbc & Hircb).
    destruct (linD _ _ Hba) as (ib2 & ia & Hvalb2 & Hvala & Hinsab & Hirba).
    assert (Heqb : ib1 = ib2) by (eapply def_push_once; [exact Hvalb1 | exact Hvalb2]).
    subst ib2.
    assert (Hpushia : is_push val ia) by (exists ra; done).
    assert (Hpushib : is_push val ib1) by (exists rb; done).
    assert (Hpushic : is_push val ic) by (exists rc; done).
    assert (Hpopra : is_pop val ra) by (exists ia; done).
    assert (Hpoprb : is_pop val rb) by (exists ib1; done).
    assert (Hpoprc : is_pop val rc) by (exists ic; done).
    (* We need to show ins ia ic and ir ic ra *)
    (* ins ia ic: from lem_ins_transitive and Hinsab, Hinsbc *)
    assert (Hinsac : ins ia ic) by (by eapply lem_ins_transitive).
    (* ir ic ra: We have Hircb : ir ic rb and Hirba : ir ib1 ra *)
    (* We need to use ipr_ooo_ir or similar to derive a contradiction or ir ic ra *)
    destruct (decide (ir ic ra)) as [Hicra|Hnicra].
    - apply (linI ic rc ia ra); done.
    - (* ¬ ir ic ra, so ir ra ic *)
      assert (Hraic : ir ra ic) by (by apply not_ir_push_pop_ir).
      exfalso.
      by eapply (ipr_ooo_ir ia ra ib1 rb ic).
  Qed.

  (* remove_relaxed_stack.thy:380-381 *)
  Lemma lem_prUlin_irreflexive : Irreflexive (pre ∪ lin).
  Proof.
    intros x [Hpre|Hlin].
    - by eapply wf_pre_irreflexive.
    - by eapply lem_lin_irreflexive.
  Qed.

  (* remove_relaxed_stack.thy:383-402 *)
  Lemma lem_lin_u_pop_ir_transitive : Transitive (lin ∪ pop_ir).
  Proof.
    intros x y z [Hlinxy|Hpopxy] [Hlinyz|Hpopyz].
    - left. by eapply lem_lin_transitive.
    - (* lin x y, pop_ir y z *)
      destruct (pop_irD _ _ Hpopyz) as (Hpopy & Hpopz & (ic & Hyic & Hicz)).
      destruct (linD _ _ Hlinxy) as (ix & iy & Hvalx & Hvaly & Hinsyx & Hirxy).
      assert (Hpopx : is_pop val x) by (exists ix; done).
      destruct (decide (ir x ic)) as [Hxic|Hnxic].
      + right. apply (pop_irI _ _ ic); done.
      + assert (Hpushic : is_push val ic) by (by apply (ir_push_and_pop3 _ _ Hyic)).
        assert (Hicx : ir ic x) by (by apply not_ir_pop_push_ir).
        exfalso.
        by eapply (ipr_ooo_ir iy y ix x ic).
    - (* pop_ir x y, lin y z *)
      destruct (pop_irD _ _ Hpopxy) as (Hpopx & Hpopy & (ic & Hxic & Hicy)).
      destruct (linD _ _ Hlinyz) as (iy & iz & Hvaly & Hvalz & Hinszy & Hiryz).
      (* linD gives: Hvaly : val iy y, Hvalz : val iz z, Hinszy : ins iz iy, Hiryz : ir iy z *)
      assert (Hpopz : is_pop val z) by (exists iz; done).
      destruct (decide (ir ic z)) as [Hicz|Hnicz].
      + right. apply (pop_irI _ _ ic); done.
      + assert (Hpushic : is_push val ic) by (by apply (ir_push_and_pop3 _ _ Hxic)).
        assert (Hzic : ir z ic) by (by apply not_ir_push_pop_ir).
        exfalso.
        (* ipr_ooo_ir says: val ia ra → val ib rb → ins ia ib → ir ib ra → ¬(ir ra ic ∧ ir ic rb) *)
        (* We have: val iz z, val iy y, ins iz iy, ir iy z (Hiryz) *)
        (* We need: ¬(ir z ic ∧ ir ic y) *)
        (* But we have Hzic : ir z ic. We need ir ic y. *)
        (* Hicy : ir ic y from pop_ir *)
        eapply (ipr_ooo_ir iz z iy y ic); [done | done | done | done | split; done].
    - right. by eapply lem_pop_ir_transitive.
  Qed.

  (* remove_relaxed_stack.thy:404-405 *)
  Lemma lem_lin_u_pop_ir_irreflexive : Irreflexive (lin ∪ pop_ir).
  Proof.
    intros x [Hlin|Hpop].
    - by eapply lem_lin_irreflexive.
    - by eapply lem_pop_ir_irreflexive.
  Qed.

  (* remove_relaxed_stack.thy:407-431 *)
  Lemma prUlinD a e : tc (pre ∪ lin) a e →
    pre a e ∨ lin a e ∨
    (∃ b, lin a b ∧ pre b e) ∨
    (∃ b, pre a b ∧ lin b e) ∨
    (∃ b c, lin a b ∧ pre b c ∧ lin c e).
  Proof.
    intros Htc.
    induction Htc as [x y Hxy|x y z Hxy Hyz IHyz].
    - destruct Hxy as [Hpre|Hlin].
      + left. done.
      + right. left. done.
    - destruct Hxy as [Hprexy|Hlinxy].
      + (* pre x y *)
        destruct IHyz as [Hpreyz|[Hlinyz|[(b & Hlinb & Hpreb)|[(b & Hpreb & Hlinb)|(b & c & Hlinb & Hprebc & Hlinc)]]]].
        * left. etrans; done.
        * right. right. right. left. exists y. done.
        * (* pre x y, lin y b, pre b z *)
          destruct (abcd x y b z Hprexy Hpreb) as [Hprexz|Hprebx].
          -- left. done.
          -- destruct (linD _ _ Hlinb) as (iy & ib & Hvaly & Hvalb & Hinsby & Hiryb).
             exfalso.
             eapply (ipr_ooo ib b iy y); [done|done|done|done|done].
        * (* pre x y, pre y b, lin b z *)
          right. right. right. left. exists b. split; [|done].
          etrans; done.
        * (* pre x y, lin y b, pre b c, lin c z *)
          destruct (abcd x y b c Hprexy Hprebc) as [Hprexc|Hprebx].
          -- right. right. right. left. exists c. done.
          -- destruct (linD _ _ Hlinb) as (iy & ib & Hvaly & Hvalb & Hinsby & Hiryb).
             exfalso.
             eapply (ipr_ooo ib b iy y); [done|done|done|done|done].
      + (* lin x y *)
        destruct IHyz as [Hpreyz|[Hlinyz|[(b & Hlinb & Hpreb)|[(b & Hpreb & Hlinb)|(b & c & Hlinb & Hprebc & Hlinc)]]]].
        * (* lin x y, pre y z *)
          right. right. left. exists y. done.
        * (* lin x y, lin y z *)
          right. left. eapply lem_lin_transitive; done.
        * (* lin x y, lin y b, pre b z *)
          right. right. left. exists b. split; [|done].
          eapply lem_lin_transitive; done.
        * (* lin x y, pre y b, lin b z *)
          right. right. right. right. exists y, b. done.
        * (* lin x y, lin y b, pre b c, lin c z *)
          right. right. right. right. exists b, c. split; [|done].
          eapply lem_lin_transitive; done.
  Qed.

  (* remove_relaxed_stack.thy:433-451 *)
  Lemma lem_prUlin_acyclic : Acyclic (pre ∪ lin).
  Proof.
    intros x Htc.
    apply prUlinD in Htc.
    destruct Htc as [Hpre|[Hlin|[(b & Hlinxb & Hprebx)|[(b & Hprexb & Hlinbx)|(b & c & Hlinxb & Hprebc & Hlincx)]]]].
    - by eapply wf_pre_irreflexive.
    - by eapply lem_lin_irreflexive.
    - (* lin x b, pre b x *)
      destruct (linD _ _ Hlinxb) as (ix & ib & Hvalx & Hvalb & Hinsbx & Hirxb).
      eapply (ipr_ooo ib b ix x); [done|done|done|done|done].
    - (* pre x b, lin b x *)
      destruct (linD _ _ Hlinbx) as (ib & ix & Hvalb & Hvalx & Hinsxb & Hirbx).
      eapply (ipr_ooo ix x ib b); [done|done|done|done|done].
    - (* lin x b, pre b c, lin c x *)
      assert (Hlincb : lin c b) by (eapply lem_lin_transitive; [exact Hlincx | exact Hlinxb]).
      destruct (linD _ _ Hlincb) as (ic & ib & Hvalc & Hvalb & Hinsbc & Hircb).
      eapply (ipr_ooo ib b ic c); [done|done|done|done|done].
  Qed.

  (* remove_relaxed_stack.thy:453-462 *)
  Lemma lem_pre_then_not_pop_ir a b : pre a b → pop_ir b a → False.
  Proof.
    intros Hpre (Hpopb & Hpopa & (ic & Hbic & Hica)).
    assert (Htc : tc (pre ∪ ir) a a).
    { eapply tc_l; [left; exact Hpre|].
      eapply tc_l; [right; exact Hbic|].
      apply tc_once. right. exact Hica. }
    eapply rrs_pr_u_ir_acyclic. exact Htc.
  Qed.

  (* remove_relaxed_stack.thy:464-518 *)
  Lemma prUirUlinD a b : tc (pre ∪ (lin ∪ pop_ir)) a b →
    (pre ∪ (lin ∪ pop_ir)) a b ∨
    (∃ c, pre a c ∧ (lin ∪ pop_ir) c b) ∨
    (∃ c, (lin ∪ pop_ir) a c ∧ pre c b) ∨
    (∃ c d, (lin ∪ pop_ir) a c ∧ pre c d ∧ (lin ∪ pop_ir) d b).
  Proof.
    intros Htc.
    induction Htc as [x y Hxy|x y z Hxy Hyz IHyz].
    - left. done.
    - destruct Hxy as [Hprexy|[Hlinxy|Hpopxy]].
      + (* pre x y *)
        destruct IHyz as [Hyz'|[(c & Hpreyc & Hcz)|[(c & Hyc & Hprecz)|
                          (c & d & Hyc & Hprecd & Hdz)]]].
        * (* (pre ∪ (lin ∪ pop_ir)) y z *)
          destruct Hyz' as [Hpreyz|[Hlinyz|Hpopyz]].
          -- left. left. etrans; done.
          -- right. left. exists y. split; [done|left; done].
          -- right. left. exists y. split; [done|right; done].
        * (* ∃ c, pre y c ∧ (lin ∪ pop_ir) c z *)
          right. left. exists c. split; [|done]. etrans; done.
        * (* ∃ c, (lin ∪ pop_ir) y c ∧ pre c z *)
          destruct (abcd x y c z Hprexy Hprecz) as [Hprexz|Hprecy].
          -- left. left. done.
          -- destruct Hyc as [Hlinyc|Hpopyc].
             ++ destruct (linD _ _ Hlinyc) as (iy & ic & Hvaly & Hvalc & Hinscy & Hiryc).
                exfalso. eapply (ipr_ooo ic c iy y); [done|done|done|done|done].
             ++ exfalso. eapply lem_pre_then_not_pop_ir; [exact Hprecy|done].
        * (* ∃ c d, (lin ∪ pop_ir) y c ∧ pre c d ∧ (lin ∪ pop_ir) d z *)
          destruct (abcd x y c d Hprexy Hprecd) as [Hprexd|Hprecx].
          -- right. left. exists d. done.
          -- destruct Hyc as [Hlinyc|Hpopyc].
             ++ destruct (linD _ _ Hlinyc) as (iy & ic & Hvaly & Hvalc & Hinscy & Hiryc).
                exfalso. eapply (ipr_ooo ic c iy y); [done|done|done|done|done].
             ++ exfalso. eapply lem_pre_then_not_pop_ir; [exact Hprecx|done].
      + (* lin x y *)
        destruct IHyz as [Hyz'|[(c & Hpreyc & Hcz)|[(c & Hyc & Hprecz)|
                          (c & d & Hyc & Hprecd & Hdz)]]].
        * destruct Hyz' as [Hpreyz|[Hlinyz|Hpopyz]].
          -- right. right. left. exists y. split; [left; done|done].
          -- left. right. left. eapply lem_lin_transitive; done.
          -- left. right. apply (lem_lin_u_pop_ir_transitive x y z); [left; done|right; done].
        * (* lin x y, pre y c, (lin ∪ pop_ir) c z *)
          right. right. right. exists y, c. split; [left; done|done].
        * (* lin x y, (lin ∪ pop_ir) y c, pre c z *)
          right. right. left. exists c. split; [|done].
          apply (lem_lin_u_pop_ir_transitive x y c); [left; done|done].
        * (* lin x y, (lin ∪ pop_ir) y c, pre c d, (lin ∪ pop_ir) d z *)
          right. right. right. exists c, d. split; [|done].
          apply (lem_lin_u_pop_ir_transitive x y c); [left; done|done].
      + (* pop_ir x y *)
        destruct IHyz as [Hyz'|[(c & Hpreyc & Hcz)|[(c & Hyc & Hprecz)|
                          (c & d & Hyc & Hprecd & Hdz)]]].
        * destruct Hyz' as [Hpreyz|[Hlinyz|Hpopyz]].
          -- right. right. left. exists y. split; [right; done|done].
          -- left. right. apply (lem_lin_u_pop_ir_transitive x y z); [right; done|left; done].
          -- left. right. right. eapply lem_pop_ir_transitive; done.
        * (* pop_ir x y, pre y c, (lin ∪ pop_ir) c z *)
          right. right. right. exists y, c. split; [right; done|done].
        * (* pop_ir x y, (lin ∪ pop_ir) y c, pre c z *)
          right. right. left. exists c. split; [|done].
          apply (lem_lin_u_pop_ir_transitive x y c); [right; done|done].
        * (* pop_ir x y, (lin ∪ pop_ir) y c, pre c d, (lin ∪ pop_ir) d z *)
          right. right. right. exists c, d. split; [|done].
          apply (lem_lin_u_pop_ir_transitive x y c); [right; done|done].
  Qed.

  (* remove_relaxed_stack.thy:520-552 *)
  Lemma lem_pr_ir_lin_acyclic : Acyclic (pre ∪ (lin ∪ pop_ir)).
  Proof.
    intros x Htc.
    apply prUirUlinD in Htc.
    destruct Htc as [Hxx|[(c & Hprexc & Hcx)|[(c & Hxc & Hprecx)|
                      (c & d & Hxc & Hprecd & Hdx)]]].
    - destruct Hxx as [Hprexx|[Hlinxx|Hpopxx]].
      + by eapply wf_pre_irreflexive.
      + by eapply lem_lin_irreflexive.
      + by eapply lem_pop_ir_irreflexive.
    - (* pre x c, (lin ∪ pop_ir) c x *)
      destruct Hcx as [Hlincx|Hpopcx].
      + destruct (linD _ _ Hlincx) as (ic & ix & Hvalc & Hvalx & Hinsxc & Hircx).
        eapply (ipr_ooo ix x ic c); [done|done|done|done|done].
      + eapply lem_pre_then_not_pop_ir; [exact Hprexc|done].
    - (* (lin ∪ pop_ir) x c, pre c x *)
      destruct Hxc as [Hlinxc|Hpopxc].
      + destruct (linD _ _ Hlinxc) as (ix & ic & Hvalx & Hvalc & Hinscx & Hirxc).
        eapply (ipr_ooo ic c ix x); [done|done|done|done|done].
      + eapply lem_pre_then_not_pop_ir; [exact Hprecx|done].
    - (* (lin ∪ pop_ir) x c, pre c d, (lin ∪ pop_ir) d x *)
      assert (Hdxc : (lin ∪ pop_ir) d c).
      { eapply lem_lin_u_pop_ir_transitive; [exact Hdx|exact Hxc]. }
      destruct Hdxc as [Hlindc|Hpopdc].
      + destruct (linD _ _ Hlindc) as (id & ic & Hvald & Hvalc & Hinscd & Hirdc).
        eapply (ipr_ooo ic c id d); [done|done|done|done|done].
      + eapply lem_pre_then_not_pop_ir; [exact Hprecd|done].
  Qed.

  (* remove_relaxed_stack.thy:554-556 *)
  Definition w1 : relation operation := tc (pre ∪ (lin ∪ pop_ir)).

  Local Instance w1_dec : RelDecision w1.
  Proof.
    apply tc_decision. intros a b.
    unfold relation_union, Relation_Operators.union, lin, pop_ir, ins, ins_order, is_push, is_pop.
    apply _.
  Qed.

  (* remove_relaxed_stack.thy:558-560 *)
  Definition wins1 : relation operation :=
    λ a b, is_push val a ∧ is_push val b ∧ (w1 a b ∨ (∃ c, is_pop val c ∧ w1 a c ∧ ir c b)).

  (* remove_relaxed_stack.thy:562-563 *)
  Lemma lem_trancl_w1D x y : tc w1 x y → w1 x y.
  Proof.
    intros Htc.
    unfold w1.
    induction Htc as [a b Hab|a b c Hab Hbc IHbc].
    - unfold w1 in Hab. done.
    - unfold w1 in Hab. eapply tc_transitive; [exact Hab | exact IHbc].
  Qed.

  (* remove_relaxed_stack.thy:565-566 *)
  Lemma lem_w1_transitive : Transitive w1.
  Proof.
    intros x y z Hxy Hyz.
    unfold w1 in *.
    by eapply tc_transitive.
  Qed.

  (* remove_relaxed_stack.thy:568-569 *)
  Lemma lem_w1_irreflexive : Irreflexive w1.
  Proof.
    intros x Hxx.
    unfold w1 in Hxx.
    eapply lem_pr_ir_lin_acyclic. exact Hxx.
  Qed.

  (* remove_relaxed_stack.thy:571-572 *)
  Lemma lem_w1_acyclic : Acyclic w1.
  Proof.
    intros x Htc.
    apply lem_trancl_w1D in Htc.
    by eapply lem_w1_irreflexive.
  Qed.

  (* remove_relaxed_stack.thy:574-578 *)
  Lemma w1D a b : w1 a b →
    (pre ∪ (lin ∪ pop_ir)) a b ∨
    (∃ c, pre a c ∧ (lin ∪ pop_ir) c b) ∨
    (∃ c, (lin ∪ pop_ir) a c ∧ pre c b) ∨
    (∃ c d, (lin ∪ pop_ir) a c ∧ pre c d ∧ (lin ∪ pop_ir) d b).
  Proof.
    intros Hw1.
    unfold w1 in Hw1.
    apply prUirUlinD. done.
  Qed.

  (* remove_relaxed_stack.thy:580-588 *)
  Lemma lem_w1_then_push_or_pop1 a b : w1 a b → is_push val a ∨ is_pop val a.
  Proof.
    intros Hw1.
    apply w1D in Hw1.
    destruct Hw1 as [Hab|[(c & Hpreac & Hcb)|[(c & Hac & Hprecb)|(c & d & Hac & Hprecd & Hdb)]]].
    - destruct Hab as [Hpre|[Hlin|Hpop]].
      + destruct (def_push_or_pop _ _ Hpre) as [[e [He|He]] _].
        * left. exists e. done.
        * right. exists e. done.
      + destruct (linD _ _ Hlin) as (ia & ib & Hvala & Hvalb & Hins & Hir).
        right. exists ia. done.
      + destruct (pop_irD _ _ Hpop) as (Hpopa & _ & _). right. done.
    - destruct (def_push_or_pop _ _ Hpreac) as [[e [He|He]] _].
      + left. exists e. done.
      + right. exists e. done.
    - destruct Hac as [Hlin|Hpop].
      + destruct (linD _ _ Hlin) as (ia & ic & Hvala & Hvalc & Hins & Hir).
        right. exists ia. done.
      + destruct (pop_irD _ _ Hpop) as (Hpopa & _ & _). right. done.
    - destruct Hac as [Hlin|Hpop].
      + destruct (linD _ _ Hlin) as (ia & ic & Hvala & Hvalc & Hins & Hir).
        right. exists ia. done.
      + destruct (pop_irD _ _ Hpop) as (Hpopa & _ & _). right. done.
  Qed.

  (* remove_relaxed_stack.thy:590-598 *)
  Lemma lem_w1_then_push_or_pop2 a b : w1 a b → is_push val b ∨ is_pop val b.
  Proof.
    intros Hw1.
    apply w1D in Hw1.
    destruct Hw1 as [Hab|[(c & Hpreac & Hcb)|[(c & Hac & Hprecb)|(c & d & Hac & Hprecd & Hdb)]]].
    - destruct Hab as [Hpre|[Hlin|Hpop]].
      + destruct (def_push_or_pop _ _ Hpre) as [_ [e [He|He]]].
        * left. exists e. done.
        * right. exists e. done.
      + destruct (linD _ _ Hlin) as (ia & ib & Hvala & Hvalb & Hins & Hir).
        right. exists ib. done.
      + destruct (pop_irD _ _ Hpop) as (_ & Hpopb & _). right. done.
    - destruct Hcb as [Hlin|Hpop].
      + destruct (linD _ _ Hlin) as (ic & ib & Hvalc & Hvalb & Hins & Hir).
        right. exists ib. done.
      + destruct (pop_irD _ _ Hpop) as (_ & Hpopb & _). right. done.
    - destruct (def_push_or_pop _ _ Hprecb) as [_ [e [He|He]]].
      + left. exists e. done.
      + right. exists e. done.
    - destruct Hdb as [Hlin|Hpop].
      + destruct (linD _ _ Hlin) as (id & ib & Hvald & Hvalb & Hins & Hir).
        right. exists ib. done.
      + destruct (pop_irD _ _ Hpop) as (_ & Hpopb & _). right. done.
  Qed.

  (* remove_relaxed_stack.thy:600-624 *)
  Lemma lem_w1_push_then_pr a b : w1 a b → is_push val a → is_push val b → pre a b.
  Proof.
    intros Hw1 Hpusha Hpushb.
    apply w1D in Hw1.
    destruct Hw1 as [Hab|[(c & Hpreac & Hcb)|[(c & Hac & Hprecb)|(c & d & Hac & Hprecd & Hdb)]]].
    - destruct Hab as [Hpre|[Hlin|Hpop]].
      + done.
      + destruct (linD _ _ Hlin) as (ia & ib & Hvala & Hvalb & Hins & Hir).
        destruct Hpusha as [ra Hvara].
        exfalso. eapply def_val_order; [exact Hvara|exists ia; left; done].
      + destruct (pop_irD _ _ Hpop) as (Hpopa & Hpopb & _).
        destruct Hpusha as [ra Hvara]. destruct Hpopa as [ia Hvaia].
        exfalso. eapply def_val_order; [exact Hvara|exists ia; left; done].
    - destruct Hcb as [Hlin|Hpop].
      + destruct (linD _ _ Hlin) as (ic & ib & Hvalc & Hvalb & Hins & Hir).
        destruct Hpushb as [rb Hvarb].
        exfalso. eapply def_val_order; [exact Hvarb|exists ib; left; done].
      + destruct (pop_irD _ _ Hpop) as (Hpopc & Hpopb & _).
        destruct Hpushb as [rb Hvarb]. destruct Hpopb as [ib Hvbib].
        exfalso. eapply def_val_order; [exact Hvarb|exists ib; left; done].
    - destruct Hac as [Hlin|Hpop].
      + destruct (linD _ _ Hlin) as (ia & ic & Hvala & Hvalc & Hins & Hir).
        destruct Hpusha as [ra Hvara].
        exfalso. eapply def_val_order; [exact Hvara|exists ia; left; done].
      + destruct (pop_irD _ _ Hpop) as (Hpopa & _ & _).
        destruct Hpusha as [ra Hvara]. destruct Hpopa as [ia Hvaia].
        exfalso. eapply def_val_order; [exact Hvara|exists ia; left; done].
    - destruct Hac as [Hlin|Hpop].
      + destruct (linD _ _ Hlin) as (ia & ic & Hvala & Hvalc & Hins & Hir).
        destruct Hpusha as [ra Hvara].
        exfalso. eapply def_val_order; [exact Hvara|exists ia; left; done].
      + destruct (pop_irD _ _ Hpop) as (Hpopa & _ & _).
        destruct Hpusha as [ra Hvara]. destruct Hpopa as [ia Hvaia].
        exfalso. eapply def_val_order; [exact Hvara|exists ia; left; done].
  Qed.

  (* remove_relaxed_stack.thy:626-680 *)
  (* Note: This proof has complex cases that require careful use of val_order
     to derive contradictions. The helper lemmas are now available in conc_his_rel.v. *)
  Lemma lem_wins1_then_ins a b : wins1 a b → ins a b.
  Proof.
    intros (Hpusha & Hpushb & [Hw1ab | (c & Hpopc & Hw1ac & Hircb)]).
    - (* Case: w1 a b directly *)
      apply lem_pr_then_ins; [done | done |].
      apply lem_w1_push_then_pr; done.
    - (* Case: exists c such that is_pop c, w1 a c, ir c b *)
      apply w1D in Hw1ac.
      destruct Hw1ac as [Hac | [(d & Hpread & Hdc) | [(d & Had & Hpredb) | (d & e & Had & Hprede & Hec)]]].
      + (* w1 a c is just (pre ∪ (lin ∪ pop_ir)) a c *)
        destruct Hac as [Hpreac | [Hlinac | Hpopirac]].
        * (* pre a c *)
          apply (insI _ _ c); done.
        * (* lin a c - contradiction: a is push, but lin relates pops *)
          exfalso.
          destruct (linD _ _ Hlinac) as (ia & ib & Hvalia & Hvalib & Hins & Hir).
          destruct Hpusha as [ra Hvara].
          eapply def_val_order; [exact Hvara | exists ia; left; done].
        * (* pop_ir a c - contradiction: a is push *)
          exfalso.
          destruct (pop_irD _ _ Hpopirac) as (Hpopa & _ & _).
          destruct Hpusha as [ra Hvara]. destruct Hpopa as [ia Hvaia].
          eapply def_val_order; [exact Hvara | exists ia; left; done].
      + (* w1 a c has pre a d and (lin ∪ pop_ir) d c *)
        destruct Hdc as [Hlindc | Hpopirdc].
        * (* lin d c *)
          destruct (linD _ _ Hlindc) as (id & ic & Hvalid & Hvalic & Hins & Hiridc).
          (* d is pop (val id d) *)
          assert (Hpopd : is_pop val d) by (exists id; done).
          (* Consider ir b d or ir d b *)
          destruct (push_pop_ordered b d Hpushb Hpopd) as [Hirbd | Hirdb].
          -- (* ir b d - contradiction via ipr_ooo_ir *)
             exfalso.
             (* ipr_ooo_ir: val ic c → val id d → ins_order ic id → ir id c → ¬(ir c b ∧ ir b d) *)
             apply (ipr_ooo_ir ic c id d b Hvalic Hvalid Hins Hiridc).
             split; done.
          -- (* ir d b - construct ins a b via insI *)
             apply (insI _ _ d); done.
        * (* pop_ir d c - construct ins a b via ir_transitive and insI *)
          destruct (pop_irD _ _ Hpopirdc) as (_ & _ & (e & Hirde & Hirec)).
          (* ir d e, ir e c, ir c b gives ir d b by ir_transitive *)
          assert (Hirdb : ir d b) by (eapply ir_transitive; [exact Hirde | exact Hirec | exact Hircb]).
          (* insI a b d: pre a d, ir d b *)
          apply (insI _ _ d); done.
      + (* w1 a c has (lin ∪ pop_ir) a d and pre d c *)
        (* a is in lin or pop_ir. But a is push. *)
        destruct Had as [Hlinad | Hpopirad].
        * (* lin a d - contradiction: a is push, lin relates pops *)
          exfalso.
          destruct (linD _ _ Hlinad) as (ia & id & Hvalia & Hvalid & Hins & Hir).
          destruct Hpusha as [ra Hvara].
          eapply def_val_order; [exact Hvara | exists ia; left; done].
        * (* pop_ir a d - contradiction: a is push, pop_ir relates pops *)
          exfalso.
          destruct (pop_irD _ _ Hpopirad) as (Hpopa & _ & _).
          destruct Hpusha as [ra Hvara]. destruct Hpopa as [ia Hvaia].
          eapply def_val_order; [exact Hvara | exists ia; left; done].
      + (* w1 a c has (lin ∪ pop_ir) a d, pre d e, (lin ∪ pop_ir) e c *)
        (* a is in lin or pop_ir. But a is push. *)
        destruct Had as [Hlinad | Hpopirad].
        * (* lin a d - contradiction *)
          exfalso.
          destruct (linD _ _ Hlinad) as (ia & id & Hvalia & Hvalid & Hins & Hir).
          destruct Hpusha as [ra Hvara].
          eapply def_val_order; [exact Hvara | exists ia; left; done].
        * (* pop_ir a d - contradiction *)
          exfalso.
          destruct (pop_irD _ _ Hpopirad) as (Hpopa & _ & _).
          destruct Hpusha as [ra Hvara]. destruct Hpopa as [ia Hvaia].
          eapply def_val_order; [exact Hvara | exists ia; left; done].
  Qed.

  (* remove_relaxed_stack.thy:682-686 *)
  Lemma lem_w1_ooo ia ra ib rb : val ia ra → val ib rb → wins1 ia ib → ir ib ra → w1 rb ra.
  Proof.
    intros Hvala Hvalb Hwins Hir.
    assert (Hins : ins ia ib) by (apply lem_wins1_then_ins; done).
    assert (Hlin : lin rb ra) by (apply (linI ib rb ia ra); done).
    unfold w1. apply tc_once. right. left. done.
  Qed.

  (* remove_relaxed_stack.thy:688-697 *)
  Lemma lem_pr_ir_then_ir a b c : is_push val a → is_push val b → is_pop val c →
    pre a b → ir b c → ir a c.
  Proof.
    intros Hpusha Hpushb Hpopc Hpre Hir.
    destruct (decide (ir a c)) as [Hirac|Hnirac]; [done|].
    assert (Hirca : ir c a) by (by apply not_ir_push_pop_ir).
    exfalso.
    assert (Htc : tc (pre ∪ ir) a a).
    { eapply tc_l; [left; exact Hpre|].
      eapply tc_l; [right; exact Hir|].
      apply tc_once. right. exact Hirca. }
    by eapply rrs_pr_u_ir_acyclic.
  Qed.

  (* remove_relaxed_stack.thy:699-700 *)
  Lemma lem_w1Uir_then_push_or_pop1 a b : (w1 ∪ ir) a b → is_push val a ∨ is_pop val a.
  Proof.
    intros [Hw1|Hir].
    - eapply lem_w1_then_push_or_pop1. exact Hw1.
    - destruct (ir_push_and_pop _ _ Hir) as [[Hpush _]|[Hpop _]]; [left|right]; done.
  Qed.

  (* remove_relaxed_stack.thy:702-703 *)
  Lemma lem_w1Uir_then_push_or_pop2 a b : (w1 ∪ ir) a b → is_push val b ∨ is_pop val b.
  Proof.
    intros [Hw1|Hir].
    - eapply lem_w1_then_push_or_pop2. exact Hw1.
    - destruct (ir_push_and_pop _ _ Hir) as [[_ Hpop]|[_ Hpush]]; [right|left]; done.
  Qed.

  (* remove_relaxed_stack.thy:705-941 *)
  (* This is a complex proof with many cases based on push/pop status.
     The Isabelle version is 230+ lines with heavy SMT automation. *)
  Lemma lem_trancl_w1UnirD a b : tc (w1 ∪ ir) a b →
    (is_push val a ∧ is_push val b ∧ (pre a b ∨ (∃ c, ir a c ∧ ir c b))) ∨
    (is_push val a ∧ is_pop val b ∧ ir a b) ∨
    (is_pop val a ∧ is_push val b ∧ ir a b) ∨
    (is_pop val a ∧ is_pop val b ∧ w1 a b).
  Proof.
    intros Htc.
    induction Htc as [x y Hxy | x y z Hxy Hyz IHyz].
    - (* Base case: (w1 ∪ ir) x y *)
      destruct (lem_w1Uir_then_push_or_pop1 _ _ Hxy) as [Hpushx|Hpopx];
      destruct (lem_w1Uir_then_push_or_pop2 _ _ Hxy) as [Hpushy|Hpopy].
      + (* x push, y push *)
        left. split; [done|split; [done|]].
        destruct Hxy as [Hw1|Hir].
        * left. apply lem_w1_push_then_pr; done.
        * (* ir x y with both push - contradiction by alternating *)
          destruct (ir_push_and_pop _ _ Hir) as [[_ Hpopy]|[Hpopx' _]].
          -- destruct Hpopy as [iy Hiy]. destruct Hpushy as [ry Hry].
             exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
          -- destruct Hpopx' as [ix Hix]. destruct Hpushx as [rx Hrx].
             exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
      + (* x push, y pop *)
        right. left. split; [done|split; [done|]].
        destruct Hxy as [Hw1|Hir]; [|done].
        (* w1 x y with x push, y pop - derive ir via w1D *)
        apply w1D in Hw1.
        destruct Hw1 as [Hxy' | [(c & Hprexc & Hcy) | [(c & Hxc & Hprecy) | (c & d & Hxc & Hprecd & Hdy)]]].
        * (* (pre ∪ (lin ∪ pop_ir)) x y *)
          destruct Hxy' as [Hpre | [Hlin | Hpopir]].
          -- apply (lem_push_pr_pop_then_ir x y Hpushx Hpopy Hpre).
          -- destruct (linD _ _ Hlin) as (ix & _ & Hvalix & _ & _ & _).
             destruct Hpushx as [rx Hrx].
             exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
          -- destruct (pop_irD _ _ Hpopir) as (Hpopx' & _ & _).
             destruct Hpopx' as [ix Hix]. destruct Hpushx as [rx Hrx].
             exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
        * (* pre x c, (lin ∪ pop_ir) c y *)
          destruct Hcy as [Hlincy | Hpopircy].
          -- (* lin c y - complex case *)
             destruct (linD _ _ Hlincy) as (ic & iy & Hvalic & Hvaliy & Hinsiyic & Hiricy).
             assert (Hpopc : is_pop val c) by (exists ic; done).
             assert (Hirxc : ir x c) by (apply lem_push_pr_pop_then_ir; done).
             destruct (push_pop_ordered x y Hpushx Hpopy) as [Hirxy|Hiryx]; [done|].
             (* Contradiction via cycle *)
             exfalso.
             assert (Hpushic : is_push val ic) by (exists c; done).
             assert (Hiricc : ir ic c) by (eapply ir_transitive; [exact Hiricy|exact Hiryx|exact Hirxc]).
             assert (Hpreic_c : pre ic c) by (apply rrs_val_then_pr; done).
             destruct (push_pop_ordered ic c Hpushic Hpopc) as [_|Hircic].
             ++ (* Use ipr_ooo_ir: ins iy ic, ir ic y gives ¬(ir y x ∧ ir x c) *)
                eapply (ipr_ooo_ir iy y ic c x); [exact Hvaliy|exact Hvalic|exact Hinsiyic|exact Hiricy|].
                split; [exact Hiryx|exact Hirxc].
             ++ assert (Htc_icic : tc (pre ∪ ir) ic ic).
                { eapply tc_l; [left; exact Hpreic_c|apply tc_once; right; exact Hircic]. }
                eapply rrs_pr_u_ir_acyclic. exact Htc_icic.
          -- (* pop_ir c y *)
             destruct (pop_irD _ _ Hpopircy) as (Hpopc & _ & (e & Hirce & Hirey)).
             assert (Hirxc : ir x c) by (apply lem_push_pr_pop_then_ir; done).
             eapply ir_transitive; [exact Hirxc|exact Hirce|exact Hirey].
        * (* (lin ∪ pop_ir) x c - x is push, contradiction *)
          destruct Hxc as [Hlinxc | Hpopirxc].
          -- destruct (linD _ _ Hlinxc) as (ix & _ & Hvalix & _ & _ & _).
             destruct Hpushx as [rx Hrx].
             exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
          -- destruct (pop_irD _ _ Hpopirxc) as (Hpopx' & _ & _).
             destruct Hpopx' as [ix Hix]. destruct Hpushx as [rx Hrx].
             exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
        * destruct Hxc as [Hlinxc | Hpopirxc].
          -- destruct (linD _ _ Hlinxc) as (ix & _ & Hvalix & _ & _ & _).
             destruct Hpushx as [rx Hrx].
             exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
          -- destruct (pop_irD _ _ Hpopirxc) as (Hpopx' & _ & _).
             destruct Hpopx' as [ix Hix]. destruct Hpushx as [rx Hrx].
             exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
      + (* x pop, y push *)
        right. right. left. split; [done|split; [done|]].
        destruct Hxy as [Hw1|Hir]; [|done].
        apply w1D in Hw1.
        destruct Hw1 as [Hxy' | [(c & Hprexc & Hcy) | [(c & Hxc & Hprecy) | (c & d & Hxc & Hprecd & Hdy)]]].
        * destruct Hxy' as [Hpre | [Hlin | Hpopir]].
          -- apply (lem_pop_pr_push_then_ir x y Hpopx Hpushy Hpre).
          -- (* lin x y means val iy y, conflicting with y being push *)
             destruct (linD _ _ Hlin) as (_ & iy & _ & Hvaliy & _ & _).
             destruct Hpushy as [ry Hry].
             exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
          -- destruct (pop_irD _ _ Hpopir) as (_ & Hpopy' & _).
             destruct Hpopy' as [iy Hiy]. destruct Hpushy as [ry Hry].
             exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
        * destruct Hcy as [Hlincy | Hpopircy].
          -- destruct (linD _ _ Hlincy) as (_ & iy & _ & Hvaliy & _ & _).
             destruct Hpushy as [ry Hry].
             exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
          -- destruct (pop_irD _ _ Hpopircy) as (_ & Hpopy' & _).
             destruct Hpopy' as [iy Hiy]. destruct Hpushy as [ry Hry].
             exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
        * destruct Hxc as [Hlinxc | Hpopirxc].
          -- (* lin x c, pre c y - derive ir x y *)
             destruct (linD _ _ Hlinxc) as (ix & ic & Hvalix & Hvalic & Hinsicix & Hirixc).
             assert (Hpopc : is_pop val c) by (exists ic; done).
             assert (Hircy : ir c y) by (apply lem_pop_pr_push_then_ir; done).
             (* Use ipr_ooo_ir: ins ic ix, ir ix c gives ¬(ir c y ∧ ir y x) *)
             (* So if ir y x, we get contradiction with ir c y *)
             destruct (decide (ir x y)) as [Hirxy|Hnirxy]; [done|].
             (* ¬ir x y with x pop, y push gives ir y x *)
             assert (Hiryx : ir y x) by (by apply not_ir_pop_push_ir).
             exfalso.
             eapply (ipr_ooo_ir ic c ix x y); [exact Hvalic|exact Hvalix|exact Hinsicix|exact Hirixc|].
             split; [exact Hircy|exact Hiryx].
          -- destruct (pop_irD _ _ Hpopirxc) as (Hpopx' & Hpopc & (e & Hirxe & Hirec)).
             assert (Hircy : ir c y) by (apply lem_pop_pr_push_then_ir; done).
             eapply ir_transitive; [exact Hirxe|exact Hirec|exact Hircy].
        * destruct Hdy as [Hlindy | Hpopirdy].
          -- destruct (linD _ _ Hlindy) as (_ & iy & _ & Hvaliy & _ & _).
             destruct Hpushy as [ry Hry].
             exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
          -- destruct (pop_irD _ _ Hpopirdy) as (_ & Hpopy' & _).
             destruct Hpopy' as [iy Hiy]. destruct Hpushy as [ry Hry].
             exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
      + (* x pop, y pop *)
        right. right. right. split; [done|split; [done|]].
        destruct Hxy as [Hw1|Hir]; [done|].
        destruct (ir_push_and_pop _ _ Hir) as [[Hpushx' _]|[_ Hpushy']].
        * destruct Hpushx' as [rx Hrx]. destruct Hpopx as [ix Hix].
          exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
        * destruct Hpushy' as [ry Hry]. destruct Hpopy as [iy Hiy].
          exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
    - (* Step case: (w1 ∪ ir) x y, tc (w1 ∪ ir) y z, IH for y z *)
      destruct (lem_w1Uir_then_push_or_pop2 _ _ Hxy) as [Hpushy|Hpopy];
      destruct (lem_w1Uir_then_push_or_pop1 _ _ Hxy) as [Hpushx|Hpopx].
      + (* x push, y push *)
        destruct IHyz as [(Hpushy' & Hpushz & Hyz_order) | [(Hpushy' & Hpopz & Hiryz) | [(Hpopy' & _ & _) | (Hpopy' & _ & _)]]];
        try (destruct Hpopy' as [iy Hiy]; destruct Hpushy as [ry Hry];
             exfalso; eapply def_val_order; [exact Hry|exists iy; left; done]).
        * (* push y, push z *)
          left. split; [done|split; [done|]].
          destruct Hyz_order as [Hpreyz | (c & Hiryc & Hircz)].
          -- destruct Hxy as [Hw1xy|Hirxy].
             ++ left. eapply wf_pre_transitive; [apply lem_w1_push_then_pr; done|exact Hpreyz].
             ++ destruct (ir_push_and_pop _ _ Hirxy) as [[_ Hpopy']|[Hpopx' _]].
                ** destruct Hpopy' as [iy Hiy]; destruct Hpushy as [ry Hry].
                   exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
                ** destruct Hpopx' as [ix Hix]; destruct Hpushx as [rx Hrx].
                   exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
          -- destruct Hxy as [Hw1xy|Hirxy].
             ++ assert (Hprexy : pre x y) by (apply lem_w1_push_then_pr; done).
                assert (Hpopc : is_pop val c) by (apply (ir_push_and_pop1 _ _ Hiryc); done).
                assert (Hirxc : ir x c) by (apply lem_pr_ir_then_ir with (b := y); done).
                right. exists c. split; [exact Hirxc|exact Hircz].
             ++ destruct (ir_push_and_pop _ _ Hirxy) as [[_ Hpopy']|[Hpopx' _]].
                ** destruct Hpopy' as [iy Hiy]; destruct Hpushy as [ry Hry].
                   exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
                ** destruct Hpopx' as [ix Hix]; destruct Hpushx as [rx Hrx].
                   exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
        * (* push y, pop z *)
          right. left. split; [done|split; [done|]].
          destruct Hxy as [Hw1xy|Hirxy].
          -- assert (Hprexy : pre x y) by (apply lem_w1_push_then_pr; done).
             apply lem_pr_ir_then_ir with (b := y); done.
          -- destruct (ir_push_and_pop _ _ Hirxy) as [[_ Hpopy']|[Hpopx' _]].
             ++ destruct Hpopy' as [iy Hiy]; destruct Hpushy as [ry Hry].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
             ++ destruct Hpopx' as [ix Hix]; destruct Hpushx as [rx Hrx].
                exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
      + (* x pop, y push *)
        destruct IHyz as [(Hpushy' & Hpushz & Hyz_order) | [(Hpushy' & Hpopz & Hiryz) | [(Hpopy' & _ & _) | (Hpopy' & _ & _)]]];
        try (destruct Hpopy' as [iy Hiy]; destruct Hpushy as [ry Hry];
             exfalso; eapply def_val_order; [exact Hry|exists iy; left; done]).
        * right. right. left. split; [done|split; [done|]].
          (* First derive ir x y from (w1 ∪ ir) x y *)
          assert (Hirxy : ir x y).
          { destruct Hxy as [Hw1xy|Hirxy]; [|done].
            apply w1D in Hw1xy.
            destruct Hw1xy as [Hxy' | [(c & Hprexc & Hcy) | [(c & Hxc & Hprecy) | (c & d & Hxc & Hprecd & Hdy)]]].
            - destruct Hxy' as [Hpre | [Hlin | Hpopir]].
              + apply (lem_pop_pr_push_then_ir x y Hpopx Hpushy Hpre).
              + (* lin x y means val iy y, conflicting with y being push *)
                destruct (linD _ _ Hlin) as (_ & iy & _ & Hvaliy & _ & _).
                destruct Hpushy as [ry Hry].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
              + destruct (pop_irD _ _ Hpopir) as (_ & Hpopy' & _).
                destruct Hpopy' as [iy Hiy]. destruct Hpushy as [ry Hry].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
            - destruct Hcy as [Hlincy | Hpopircy].
              + destruct (linD _ _ Hlincy) as (_ & iy & _ & Hvaliy & _ & _).
                destruct Hpushy as [ry Hry].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
              + destruct (pop_irD _ _ Hpopircy) as (_ & Hpopy' & _).
                destruct Hpopy' as [iy Hiy]. destruct Hpushy as [ry Hry].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
            - destruct Hxc as [Hlinxc | Hpopirxc].
              + (* lin x c, pre c y - use ipr_ooo_ir *)
                destruct (linD _ _ Hlinxc) as (ix & ic & Hvalix & Hvalic & Hinsicix & Hirixc).
                assert (Hpopc : is_pop val c) by (exists ic; done).
                assert (Hircy : ir c y) by (apply lem_pop_pr_push_then_ir; done).
                destruct (decide (ir x y)) as [Hirxy|Hnirxy]; [done|].
                assert (Hiryx : ir y x) by (by apply not_ir_pop_push_ir).
                exfalso.
                eapply (ipr_ooo_ir ic c ix x y); [exact Hvalic|exact Hvalix|exact Hinsicix|exact Hirixc|].
                split; [exact Hircy|exact Hiryx].
              + destruct (pop_irD _ _ Hpopirxc) as (Hpopx' & Hpopc & (e & Hirxe & Hirec)).
                assert (Hircy : ir c y) by (apply lem_pop_pr_push_then_ir; done).
                eapply ir_transitive; [exact Hirxe|exact Hirec|exact Hircy].
            - destruct Hdy as [Hlindy | Hpopirdy].
              + (* lin d y - val iy y conflicts with y being push *)
                destruct (linD _ _ Hlindy) as (_ & iy & _ & Hvaliy & _ & _).
                destruct Hpushy as [ry Hry].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
              + destruct (pop_irD _ _ Hpopirdy) as (_ & Hpopy' & _).
                destruct Hpopy' as [iy Hiy]. destruct Hpushy as [ry Hry].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; done]. }
          (* Now use Hirxy with Hyz_order - goal is ir x z with x pop, z push *)
          destruct Hyz_order as [Hpreyz | (c & Hiryc & Hircz)].
             ++ (* ir x y, pre y z - derive ir x z *)
                destruct (decide (ir x z)) as [Hirxz|Hnirxz]; [done|].
                (* ¬ir x z with x pop, z push gives ir z x *)
                assert (Hirzx : ir z x) by (by apply not_ir_pop_push_ir).
                (* y --pre-> z --ir-> x --ir-> y forms a cycle *)
                exfalso.
                assert (Htc : tc (pre ∪ ir) y y).
                { eapply tc_l; [left; exact Hpreyz|].
                  eapply tc_l; [right; exact Hirzx|].
                  apply tc_once. right. exact Hirxy. }
                eapply rrs_pr_u_ir_acyclic. exact Htc.
             ++ eapply ir_transitive; [exact Hirxy|exact Hiryc|exact Hircz].
        * (* x pop, y push, z pop - need w1 x z *)
          right. right. right. split; [done|split; [done|]].
          (* Derive ir x y from (w1 ∪ ir) x y *)
          assert (Hirxy : ir x y).
          { destruct Hxy as [Hw1xy|Hirxy]; [|done].
            apply w1D in Hw1xy.
            destruct Hw1xy as [Hxy' | [(c & Hprexc & Hcy) | [(c & Hxc & Hprecy) | (c & d & Hxc & Hprecd & Hdy)]]].
            - destruct Hxy' as [Hpre | [Hlin | Hpopir]].
              + apply (lem_pop_pr_push_then_ir x y Hpopx Hpushy Hpre).
              + (* lin x y means val iy y, conflicting with y being push *)
                destruct (linD _ _ Hlin) as (_ & iy & _ & Hvaliy & _ & _).
                destruct Hpushy as [ry Hry].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
              + destruct (pop_irD _ _ Hpopir) as (_ & Hpopy' & _).
                destruct Hpopy' as [iy Hiy]. destruct Hpushy as [ry Hry].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
            - destruct Hcy as [Hlincy | Hpopircy].
              + destruct (linD _ _ Hlincy) as (_ & iy & _ & Hvaliy & _ & _).
                destruct Hpushy as [ry Hry].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
              + destruct (pop_irD _ _ Hpopircy) as (_ & Hpopy' & _).
                destruct Hpopy' as [iy Hiy]. destruct Hpushy as [ry Hry].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
            - destruct Hxc as [Hlinxc | Hpopirxc].
              + (* lin x c, pre c y - use ipr_ooo_ir *)
                destruct (linD _ _ Hlinxc) as (ix & ic & Hvalix & Hvalic & Hinsicix & Hirixc).
                assert (Hpopc : is_pop val c) by (exists ic; done).
                assert (Hircy : ir c y) by (apply lem_pop_pr_push_then_ir; done).
                destruct (decide (ir x y)) as [Hirxy|Hnirxy]; [done|].
                assert (Hiryx : ir y x) by (by apply not_ir_pop_push_ir).
                exfalso.
                eapply (ipr_ooo_ir ic c ix x y); [exact Hvalic|exact Hvalix|exact Hinsicix|exact Hirixc|].
                split; [exact Hircy|exact Hiryx].
              + destruct (pop_irD _ _ Hpopirxc) as (Hpopx' & Hpopc & (e & Hirxe & Hirec)).
                assert (Hircy : ir c y) by (apply lem_pop_pr_push_then_ir; done).
                eapply ir_transitive; [exact Hirxe|exact Hirec|exact Hircy].
            - destruct Hdy as [Hlindy | Hpopirdy].
              + (* lin d y - val iy y conflicts with y being push *)
                destruct (linD _ _ Hlindy) as (_ & iy & _ & Hvaliy & _ & _).
                destruct Hpushy as [ry Hry].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
              + destruct (pop_irD _ _ Hpopirdy) as (_ & Hpopy' & _).
                destruct Hpopy' as [iy Hiy]. destruct Hpushy as [ry Hry].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; done]. }
          (* Now ir x y and ir y z give pop_ir x z via pop_irI *)
          assert (Hpopxz : pop_ir x z) by (apply (pop_irI _ _ y); done).
          unfold w1. apply tc_once. right. right. done.
      + (* x push, y pop *)
        destruct IHyz as [(Hpushy' & _ & _) | [(Hpushy' & _ & _) | [(Hpopy' & Hpushz & Hiryz) | (Hpopy' & Hpopz & Hw1yz)]]];
        try (destruct Hpushy' as [ry Hry]; destruct Hpopy as [iy Hiy];
             exfalso; eapply def_val_order; [exact Hry|exists iy; left; done]).
        * (* pop y, push z *)
          left. split; [done|split; [done|]].
          destruct Hxy as [Hw1xy|Hirxy].
          -- right. exists y.
             split; [|exact Hiryz].
             (* ir x y from w1 x y with x push, y pop *)
             apply w1D in Hw1xy.
             destruct Hw1xy as [Hxy' | [(c & Hprexc & Hcy) | [(c & Hxc & _) | (c & d & Hxc & _ & _)]]].
             ++ destruct Hxy' as [Hpre | [Hlin | Hpopir]].
                ** apply (lem_push_pr_pop_then_ir x y Hpushx Hpopy Hpre).
                ** destruct (linD _ _ Hlin) as (ix & _ & Hvalix & _ & _ & _).
                   destruct Hpushx as [rx Hrx].
                   exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
                ** destruct (pop_irD _ _ Hpopir) as (Hpopx' & _ & _).
                   destruct Hpopx' as [ix Hix]. destruct Hpushx as [rx Hrx].
                   exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
             ++ destruct Hcy as [Hlincy | Hpopircy].
                ** (* pre x c, lin c y - derive ir x y via push_pop_ordered *)
                   destruct (linD _ _ Hlincy) as (ic & iy & Hvalic & Hvaliy & Hinsiyic & Hiricy).
                   assert (Hpopc : is_pop val c) by (exists ic; done).
                   assert (Hirxc : ir x c) by (apply lem_push_pr_pop_then_ir; done).
                   destruct (push_pop_ordered x y Hpushx Hpopy) as [Hirxy|Hiryx]; [done|].
                   (* Use ipr_ooo_ir: ins iy ic, ir ic y gives ¬(ir y x ∧ ir x c) *)
                   exfalso.
                   eapply (ipr_ooo_ir iy y ic c x); [exact Hvaliy|exact Hvalic|exact Hinsiyic|exact Hiricy|].
                   split; [exact Hiryx|exact Hirxc].
                ** destruct (pop_irD _ _ Hpopircy) as (Hpopc & _ & (e & Hirce & Hirey)).
                   assert (Hirxc : ir x c) by (apply lem_push_pr_pop_then_ir; done).
                   eapply ir_transitive; [exact Hirxc|exact Hirce|exact Hirey].
             ++ destruct Hxc as [Hlinxc | Hpopirxc].
                ** destruct (linD _ _ Hlinxc) as (ix & _ & Hvalix & _ & _ & _).
                   destruct Hpushx as [rx Hrx].
                   exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
                ** destruct (pop_irD _ _ Hpopirxc) as (Hpopx' & _ & _).
                   destruct Hpopx' as [ix Hix]. destruct Hpushx as [rx Hrx].
                   exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
             ++ destruct Hxc as [Hlinxc | Hpopirxc].
                ** destruct (linD _ _ Hlinxc) as (ix & _ & Hvalix & _ & _ & _).
                   destruct Hpushx as [rx Hrx].
                   exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
                ** destruct (pop_irD _ _ Hpopirxc) as (Hpopx' & _ & _).
                   destruct Hpopx' as [ix Hix]. destruct Hpushx as [rx Hrx].
                   exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
          -- right. exists y. split; [exact Hirxy|exact Hiryz].
        * (* pop y, pop z - need ir x z *)
          right. left. split; [done|split; [done|]].
          (* First derive ir x y from (w1 ∪ ir) x y - same as base case *)
          assert (Hirxy : ir x y).
          { destruct Hxy as [Hw1xy|Hirxy]; [|done].
            apply w1D in Hw1xy.
            destruct Hw1xy as [Hxy' | [(c' & Hprexc' & Hc'y) | [(c' & Hxc' & Hprec'y) | (c' & d & Hxc' & Hprec'd & Hdy)]]].
            - destruct Hxy' as [Hpre | [Hlin | Hpopir]].
              + apply (lem_push_pr_pop_then_ir x y Hpushx Hpopy Hpre).
              + destruct (linD _ _ Hlin) as (ix & _ & Hvalix & _ & _ & _).
                destruct Hpushx as [rx Hrx].
                exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
              + destruct (pop_irD _ _ Hpopir) as (Hpopx' & _ & _).
                destruct Hpopx' as [ix Hix]. destruct Hpushx as [rx Hrx].
                exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
            - destruct Hc'y as [Hlinc'y | Hpopirc'y].
              + destruct (linD _ _ Hlinc'y) as (ic' & iy & Hvalic' & Hvaliy & Hinsiyic' & Hiric'y).
                assert (Hpopc' : is_pop val c') by (exists ic'; done).
                assert (Hirxc' : ir x c') by (apply lem_push_pr_pop_then_ir; done).
                destruct (push_pop_ordered x y Hpushx Hpopy) as [Hirxy|Hiryx]; [done|].
                exfalso.
                eapply (ipr_ooo_ir iy y ic' c' x); [exact Hvaliy|exact Hvalic'|exact Hinsiyic'|exact Hiric'y|].
                split; [exact Hiryx|exact Hirxc'].
              + destruct (pop_irD _ _ Hpopirc'y) as (Hpopc' & _ & (e & Hirc'e & Hirey)).
                assert (Hirxc' : ir x c') by (apply lem_push_pr_pop_then_ir; done).
                eapply ir_transitive; [exact Hirxc'|exact Hirc'e|exact Hirey].
            - destruct Hxc' as [Hlinxc' | Hpopirxc'].
              + destruct (linD _ _ Hlinxc') as (ix & _ & Hvalix & _ & _ & _).
                destruct Hpushx as [rx Hrx].
                exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
              + destruct (pop_irD _ _ Hpopirxc') as (Hpopx' & _ & _).
                destruct Hpopx' as [ix Hix]. destruct Hpushx as [rx Hrx].
                exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
            - destruct Hxc' as [Hlinxc' | Hpopirxc'].
              + destruct (linD _ _ Hlinxc') as (ix & _ & Hvalix & _ & _ & _).
                destruct Hpushx as [rx Hrx].
                exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
              + destruct (pop_irD _ _ Hpopirxc') as (Hpopx' & _ & _).
                destruct Hpopx' as [ix Hix]. destruct Hpushx as [rx Hrx].
                exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done]. }
          (* Now use push_pop_ordered x z *)
          destruct (push_pop_ordered x z Hpushx Hpopz) as [Hirxz|Hirzx]; [done|].
          (* ir z x, ir x y gives pop_ir z y *)
          exfalso.
          assert (Hpopzy : pop_ir z y) by (apply (pop_irI _ _ x); done).
          assert (Hw1zy : w1 z y).
          { unfold w1. apply tc_once. right. right. done. }
          (* w1 y z and w1 z y gives cycle contradicting lem_w1_acyclic *)
          assert (Htc : tc w1 y y).
          { eapply tc_l; [exact Hw1yz|]. apply tc_once. exact Hw1zy. }
          eapply lem_w1_acyclic. exact Htc.
      + (* x pop, y pop *)
        destruct IHyz as [(Hpushy' & _ & _) | [(Hpushy' & _ & _) | [(Hpopy' & Hpushz & Hiryz) | (Hpopy' & Hpopz & Hw1yz)]]];
        try (destruct Hpushy' as [ry Hry]; destruct Hpopy as [iy Hiy];
             exfalso; eapply def_val_order; [exact Hry|exists iy; left; done]).
        * (* pop y, push z - need ir x z *)
          right. right. left. split; [done|split; [done|]].
          destruct Hxy as [Hw1xy|Hirxy].
          -- (* w1 x y, ir y z - derive ir x z *)
             destruct (decide (ir x z)) as [Hirxz|Hnirxz]; [done|].
             (* ¬ir x z implies ir z x by not_ir_pop_push_ir *)
             assert (Hirzx : ir z x) by (by apply not_ir_pop_push_ir).
             (* ir y z and ir z x gives pop_ir y x via pop_irI *)
             exfalso.
             assert (Hpopyx : pop_ir y x) by (apply (pop_irI _ _ z); done).
             assert (Hw1yx : w1 y x).
             { unfold w1. apply tc_once. right. right. done. }
             (* w1 x y and w1 y x gives cycle *)
             assert (Htc : tc w1 x x).
             { eapply tc_l; [exact Hw1xy|]. apply tc_once. exact Hw1yx. }
             eapply lem_w1_acyclic. exact Htc.
          -- destruct (ir_push_and_pop _ _ Hirxy) as [[Hpushx' _]|[_ Hpushy']].
             ++ destruct Hpushx' as [rx Hrx]. destruct Hpopx as [ix Hix].
                exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
             ++ destruct Hpushy' as [ry Hry]. destruct Hpopy as [iy Hiy].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
        * (* pop y, pop z *)
          right. right. right. split; [done|split; [done|]].
          destruct Hxy as [Hw1xy|Hirxy].
          -- eapply lem_w1_transitive; [exact Hw1xy|exact Hw1yz].
          -- destruct (ir_push_and_pop _ _ Hirxy) as [[Hpushx' _]|[_ Hpushy']].
             ++ destruct Hpushx' as [rx Hrx]. destruct Hpopx as [ix Hix].
                exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
             ++ destruct Hpushy' as [ry Hry]. destruct Hpopy as [iy Hiy].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
  Qed.

  (* remove_relaxed_stack.thy:943-952 *)
  Lemma lem_w1_ir_acyclic : Acyclic (w1 ∪ ir).
  Proof.
    intros x Htc.
    apply lem_trancl_w1UnirD in Htc.
    destruct Htc as [(Hpushx & _ & [Hprexx|(c & Hirxc & Hircx)])|
                     [(Hpushx & Hpopx & _)|
                     [(Hpopx & Hpushx & _)|
                     (_ & _ & Hw1xx)]]].
    - (* Case: pre x x *)
      by eapply wf_pre_irreflexive.
    - (* Case: ∃ c, ir x c ∧ ir c x with x push *)
      (* From ir x c with x push: c is pop *)
      assert (Hpopc : is_pop val c) by (by apply (ir_push_and_pop1 _ _ Hirxc)).
      (* Now c pop, ir c x, ir x c gives pop_ir c c *)
      assert (Hpopcc : pop_ir c c).
      { apply (pop_irI _ _ x); [exact Hpopc|exact Hpopc|exact Hircx|exact Hirxc]. }
      (* But pop_ir is irreflexive *)
      by eapply lem_pop_ir_irreflexive.
    - (* Case: x is both push and pop *)
      destruct Hpushx as [rx Hrx]. destruct Hpopx as [ix Hix].
      exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
    - (* Case: x is both pop and push (symmetric) *)
      destruct Hpushx as [rx Hrx]. destruct Hpopx as [ix Hix].
      exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
    - (* Case: w1 x x *)
      by eapply lem_w1_irreflexive.
  Qed.

  (* remove_relaxed_stack.thy:954-955 *)
  Lemma lem_pr_in_w1 : subrelation pre w1.
  Proof.
    intros a b Hpre.
    unfold w1. apply tc_once. left. done.
  Qed.

  (* remove_relaxed_stack.thy:957-958 *)
  Lemma lem_pr_then_w1 a b : pre a b → w1 a b.
  Proof.
    apply lem_pr_in_w1.
  Qed.

  (* remove_relaxed_stack.thy:960-961 *)
  Lemma lem_lin_then_w1 a b : lin a b → w1 a b.
  Proof.
    intros Hlin.
    unfold w1. apply tc_once. right. left. done.
  Qed.

  (* remove_relaxed_stack.thy:963-964 *)
  Lemma lem_pop_ir_then_w1 a b : pop_ir a b → w1 a b.
  Proof.
    intros Hpop.
    unfold w1. apply tc_once. right. right. done.
  Qed.

  (* remove_relaxed_stack.thy:966-967 *)
  Lemma lem_same_ir a b : ¬ w1 a b → ¬ w1 b a → is_pop val a → is_pop val b →
    (∀ e, ir e a → ir e b) ∧ (∀ e, ir e b → ir e a).
  Proof.
    intros Hnw1ab Hnw1ba Hpopa Hpopb.
    split.
    - intros e Hirea.
      assert (Hpushe : is_push val e) by (by apply (ir_push_and_pop4 e a)).
      destruct (push_pop_ordered _ _ Hpushe Hpopb) as [Hireb|Hirbe]; [done|].
      exfalso.
      assert (Hpopba : pop_ir b a) by (apply (pop_irI _ _ e); done).
      apply Hnw1ba. apply lem_pop_ir_then_w1. done.
    - intros e Hireb.
      assert (Hpushe : is_push val e) by (by apply (ir_push_and_pop4 e b)).
      destruct (push_pop_ordered _ _ Hpushe Hpopa) as [Hirea|Hirae]; [done|].
      exfalso.
      assert (Hpopab : pop_ir a b) by (apply (pop_irI _ _ e); done).
      apply Hnw1ab. apply lem_pop_ir_then_w1. done.
  Qed.

  (* remove_relaxed_stack.thy:969-970 *)
  Lemma lem_w1_then_ir a b : w1 a b → is_push val a → is_pop val b → ir a b.
  Proof.
    intros Hw1 Hpusha Hpopb.
    destruct (push_pop_ordered _ _ Hpusha Hpopb) as [Hir|Hirba]; [done|].
    exfalso.
    (* We have w1 a b and ir b a, need to derive a cycle *)
    assert (Htc : tc (w1 ∪ ir) a a).
    { eapply tc_l; [left; exact Hw1|].
      apply tc_once. right. exact Hirba. }
    by eapply lem_w1_ir_acyclic.
  Qed.

  (* remove_relaxed_stack.thy:972-974 *)
  Definition w1_pop : relation operation :=
    λ a b, is_pop val a ∧ is_pop val b ∧ w1 a b.

  Local Instance w1_pop_dec : RelDecision w1_pop.
  Proof. intros a b. unfold w1_pop. apply _. Qed.

  (* remove_relaxed_stack.thy:976-978 *)
  Lemma w1_popD a b : w1_pop a b → is_pop val a ∧ is_pop val b ∧ w1 a b.
  Proof. done. Qed.

  (* remove_relaxed_stack.thy:980-982 *)
  Lemma w1_popI a b : is_pop val a → is_pop val b → w1 a b → w1_pop a b.
  Proof.
    intros Hpopa Hpopb Hw1.
    split; [done|]. split; [done|]. done.
  Qed.

  (* remove_relaxed_stack.thy:984-985 *)
  Lemma w1_pop_transitive : Transitive w1_pop.
  Proof.
    intros x y z (Hpopx & Hpopy & Hxy) (Hpopy' & Hpopz & Hyz).
    split; [done|]. split; [done|].
    eapply lem_w1_transitive; [exact Hxy|exact Hyz].
  Qed.

  (* remove_relaxed_stack.thy:987-988 *)
  Lemma w1_pop_irreflexive : Irreflexive w1_pop.
  Proof.
    intros x (Hpopx & _ & Hxx).
    by eapply lem_w1_irreflexive.
  Qed.

  (* remove_relaxed_stack.thy:990-991 *)
  Lemma w1_pop_antisymmetric : Antisymmetric operation (=) w1_pop.
  Proof.
    intros x y (Hpopx & Hpopy & Hxy) (Hpopy' & Hpopx' & Hyx).
    exfalso.
    assert (Hxx : w1 x x) by (eapply lem_w1_transitive; [exact Hxy|exact Hyx]).
    by eapply lem_w1_irreflexive.
  Qed.

  (* remove_relaxed_stack.thy:993-994 *)
  Lemma tc_w1_pop_in_w1 a b : tc w1_pop a b → w1 a b.
  Proof.
    intros Htc.
    induction Htc as [x y Hxy|x y z Hxy Hyz IHyz].
    - destruct (w1_popD _ _ Hxy) as (_ & _ & Hw1). exact Hw1.
    - destruct (w1_popD _ _ Hxy) as (_ & _ & Hw1xy).
      eapply lem_w1_transitive; [exact Hw1xy|exact IHyz].
  Qed.

  Lemma w1_pop_acyclic : Acyclic w1_pop.
  Proof.
    intros x Htc.
    apply tc_w1_pop_in_w1 in Htc.
    by eapply lem_w1_irreflexive.
  Qed.

  (* remove_relaxed_stack.thy:996-997 *)
  Lemma w1_pop_then_w1 a b : w1_pop a b → w1 a b.
  Proof.
    intros (_ & _ & Hw1). done.
  Qed.

  (* remove_relaxed_stack.thy:999-1002 *)
  Lemma trancl_w1_pop_then_trancl_w1 a b : tc (w1_pop ∪ ir) a b → tc (w1 ∪ ir) a b.
  Proof.
    intros Htc.
    induction Htc as [x y Hxy|x y z Hxy Hyz IHyz].
    - apply tc_once.
      destruct Hxy as [Hw1pop|Hir].
      + left. apply w1_pop_then_w1. done.
      + right. done.
    - eapply tc_l; [|exact IHyz].
      destruct Hxy as [Hw1pop|Hir].
      + left. apply w1_pop_then_w1. done.
      + right. done.
  Qed.

  (* remove_relaxed_stack.thy:1004-1005 *)
  Lemma w1_pop_ir_acyclic : Acyclic (w1_pop ∪ ir).
  Proof.
    intros x Htc.
    apply trancl_w1_pop_then_trancl_w1 in Htc.
    by eapply lem_w1_ir_acyclic.
  Qed.

  (* remove_relaxed_stack.thy:1007-1009 *)
  Definition pop_ops : operation → Prop := λ a, is_pop val a.

  (* remove_relaxed_stack.thy:1011-1012 *)
  Lemma pop_ops_finite : FinitePredicate pop_ops.
  Proof. apply rrs_pops_finite. Qed.

  (* remove_relaxed_stack.thy:1014-1015 *)
  Lemma only_pops_in_pop_ops a : pop_ops a → is_pop val a.
  Proof. done. Qed.

  (* Helper lemmas for the inductive proof of total order extension.
     Instead of using complex inductive predicates for finite sets/relations,
     we work directly with the list enumeration from FinitePredicate. *)

  (* When adding an edge (a,b) to an acyclic relation r where neither (a,b) nor (b,a)
     are in r and a ≠ b, the transitive closure of the extended relation is acyclic. *)
  Lemma help_acyclic r a b :
    Transitive r → Irreflexive r → Antisymmetric operation (=) r →
    ¬ r a b → ¬ r b a → a ≠ b →
    Acyclic (λ x y, (x = a ∧ y = b) ∨ r x y).
  Proof.
    intros Htrans Hirr Hanti Hnab Hnba Hneq x Htcxx.
    (* Key: any cycle in tc(r ∪ {(a,b)}) must use the edge (a,b).
       So there must be a path from b to a using only r-edges, plus the (a,b) edge. *)
    (* Track the structure of tc paths *)
    assert (Hclaim : ∀ u v, tc (λ x y, (x = a ∧ y = b) ∨ r x y) u v →
              (u = a ∧ v = b) ∨  (* just the new edge *)
              r u v ∨           (* just r-path, folded by transitivity *)
              (u = a ∧ r b v) ∨ (* new edge then r-path *)
              (r u a ∧ v = b) ∨ (* r-path then new edge *)
              (r u a ∧ r b v)). (* r-path, new edge, r-path *)
    { intros u v Htc.
      induction Htc as [u' v' Huv|u' v' w' Huv Hvw [IH1|[IH2|[IH3|[IH4|IH5]]]]].
      - destruct Huv as [[-> ->]|Hruv]; [left|right; left]; done.
      - destruct Huv as [[-> ->]|Hruv].
        + destruct IH1 as [Hva Hwb]. subst. done.
        + destruct IH1 as [-> ->]. right. right. right. left. done.
      - destruct Huv as [[-> ->]|Hruv].
        + right. right. left. done.
        + right. left. eapply Htrans; [exact Hruv|exact IH2].
      - destruct Huv as [[-> ->]|Hruv].
        + destruct IH3 as [Hba _]. done.
        + destruct IH3 as [-> Hrbw']. right. right. right. right. done.
      - destruct Huv as [[-> ->]|Hruv].
        + destruct IH4 as [Hrba _]. done.
        + destruct IH4 as [Hrv'a ->]. right. right. right. left. split; [|done].
          eapply Htrans; [exact Hruv|exact Hrv'a].
      - destruct Huv as [[-> ->]|Hruv].
        + destruct IH5 as [Hrba _]. done.
        + destruct IH5 as [Hrv'a Hrbw']. right. right. right. right. split; [|done].
          eapply Htrans; [exact Hruv|exact Hrv'a]. }
    destruct (Hclaim x x Htcxx) as [[Hxa Hxb]|[Hrxx|[[Hxa Hrbx]|[[Hrxa Hxb]|[Hrxa Hrbx]]]]].
    - subst. done.
    - eapply Hirr. exact Hrxx.
    - subst. done.
    - subst. done.
    - assert (Hrba : r b a) by (eapply Htrans; [exact Hrbx|exact Hrxa]). done.
  Qed.

  Lemma help_irreflexive r a b :
    Transitive r → Irreflexive r → Antisymmetric operation (=) r →
    ¬ r a b → ¬ r b a → a ≠ b →
    Irreflexive (tc (λ x y, (x = a ∧ y = b) ∨ r x y)).
  Proof.
    intros Htrans Hirr Hanti Hnab Hnba Hneq x Htcxx.
    eapply help_acyclic; [exact Htrans|exact Hirr|exact Hanti|exact Hnab|exact Hnba|exact Hneq|exact Htcxx].
  Qed.

  Lemma help_antisymmetric r a b :
    Transitive r → Irreflexive r → Antisymmetric operation (=) r →
    ¬ r a b → ¬ r b a → a ≠ b →
    Antisymmetric operation (=) (tc (λ x y, (x = a ∧ y = b) ∨ r x y)).
  Proof.
    intros Htrans Hirr Hanti Hnab Hnba Hneq x y Hxy Hyx.
    destruct (decide (x = y)) as [|Hne]; [done|].
    exfalso.
    assert (Htcxx : tc (λ x0 y0 : operation, (x0 = a ∧ y0 = b) ∨ r x0 y0) x x).
    { eapply tc_transitive; [exact Hxy|exact Hyx]. }
    eapply help_acyclic; [exact Htrans|exact Hirr|exact Hanti|exact Hnab|exact Hnba|exact Hneq|exact Htcxx].
  Qed.

  Lemma is_pop_preserved a b R aa ba :
    is_pop val a → is_pop val b →
    (∀ c d, R c d → is_pop val c ∧ is_pop val d) →
    (λ x y, (x = a ∧ y = b) ∨ R x y) aa ba →
    is_pop val aa ∧ is_pop val ba.
  Proof.
    intros Hpopa Hpopb HR [[-> ->]|HRab]; [done|apply HR; done].
  Qed.

  Lemma r_is_pop_then_trancl_is_pop R c d :
    (∀ a b, R a b → is_pop val a ∧ is_pop val b) →
    tc R c d → is_pop val c ∧ is_pop val d.
  Proof.
    intros HR Htc.
    induction Htc as [x y Hxy|x y z Hxy Hyz [IHy IHz]].
    - apply HR. done.
    - split; [apply HR in Hxy; destruct Hxy; done|done].
  Qed.

  (* remove_relaxed_stack.thy:1094-1095 *)
  Lemma all_in_pop_ops_rel a b : is_pop val a → is_pop val b → pop_ops a ∧ pop_ops b.
  Proof.
    intros Hpopa Hpopb. split; done.
  Qed.

  (* remove_relaxed_stack.thy:1097-1099 *)
  Lemma w1_pop_in_pop_ops_rel a b : w1_pop a b → pop_ops a ∧ pop_ops b.
  Proof.
    intros (Hpopa & Hpopb & _).
    split; done.
  Qed.

  (* remove_relaxed_stack.thy:1113-1115 *)
  Definition w2 (r : relation operation) : Prop :=
    subrelation w1_pop r ∧
    (∀ a b, pop_ops a → pop_ops b → a = b ∨ r a b ∨ r b a) ∧
    Transitive r ∧
    Irreflexive r ∧
    Antisymmetric operation (=) r ∧
    (∀ a b, r a b → is_pop val a ∧ is_pop val b).

  (* remove_relaxed_stack.thy:1117-1181
     This lemma states that w1_pop (a strict partial order on the finite set of pops)
     can be extended to a strict total order.

     The proof uses induction on the list of pop pairs.
     For each pair (a,b) of pops, we either already have them ordered, or we add
     the edge (a,b) and take the transitive closure. *)
  Lemma lem_exists_total_closure : ∃ r (_ : RelDecision r), w2 r.
  Proof.
    (* Get the enumeration of pops from FinitePredicate *)
    destruct pop_ops_finite as [enum [Hnodup Henum]].
    (* Build the list of all pairs (a,b) where a, b ∈ enum *)
    (* We prove by induction on pairs: for each pair of pops, ensure it's ordered *)
    (* Note: the totality condition is guarded by is_pop, so we don't need
       all elements in pairs to be pops - just that pops in pairs are ordered *)
    assert (Hind : ∀ pairs : list (operation * operation),
              ∃ r (_ : RelDecision r), subrelation w1_pop r ∧
                   (∀ a b, is_pop val a → is_pop val b → (a, b) ∈ pairs → a = b ∨ r a b ∨ r b a) ∧
                   Transitive r ∧ Irreflexive r ∧
                   Antisymmetric operation (=) r ∧
                   (∀ a b, r a b → is_pop val a ∧ is_pop val b)).
    { intros pairs. induction pairs as [|[c d] rest IH].
      - (* Base case: no pairs, use w1_pop *)
        exists w1_pop, _. split; [|split; [|split; [|split; [|split]]]].
        + intros x y Hxy. done.
        + intros a b _ _ Hin. exfalso. by apply (not_elem_of_nil (a, b)).
        + exact w1_pop_transitive.
        + exact w1_pop_irreflexive.
        + exact w1_pop_antisymmetric.
        + intros a b Hab. destruct (w1_popD _ _ Hab) as [Hpopa [Hpopb _]]. done.
      - (* Inductive case: pair (c,d) :: rest *)
        destruct IH as (r & Hr_dec & Hsub & Htot & Htrans & Hirr & Hanti & Hpoponly).
        (* We need to handle the case where c or d is not a pop *)
        destruct (decide (is_pop val c ∧ is_pop val d)) as [[Hpopc Hpopd]|Hnotpop].
        2: { (* c or d is not a pop - just skip this pair *)
          exists r, _.
          split; [exact Hsub|split; [|split; [|split; [|split]]]].
          - intros a b Hpopa Hpopb Hin. apply elem_of_cons in Hin.
            destruct Hin as [Heq'|Hrest].
            + (* (a,b) = (c,d) but c or d is not a pop, contradiction *)
              pose proof (f_equal fst Heq') as Ha. simpl in Ha.
              pose proof (f_equal snd Heq') as Hb. simpl in Hb.
              subst a b. exfalso. apply Hnotpop. split; done.
            + apply Htot; done.
          - exact Htrans.
          - exact Hirr.
          - exact Hanti.
          - exact Hpoponly. }
        (* Both c and d are pops *)
        (* Case 1: c = d *)
        destruct (decide (c = d)) as [Heq|Hneq].
        { subst d. exists r, _.
          split; [exact Hsub|split; [|split; [|split; [|split]]]].
          - intros a b Hpopa Hpopb Hin. apply elem_of_cons in Hin.
            destruct Hin as [Heq'|Hrest].
            + pose proof (f_equal fst Heq') as Ha. simpl in Ha.
              pose proof (f_equal snd Heq') as Hb. simpl in Hb.
              subst a b. left. reflexivity.
            + apply Htot; done.
          - exact Htrans.
          - exact Hirr.
          - exact Hanti.
          - exact Hpoponly. }
        (* Case 2: (c,d) ∈ r *)
        destruct (decide (r c d)) as [Hrcd|Hnrcd].
        { exists r, _.
          split; [exact Hsub|split; [|split; [|split; [|split]]]].
          - intros a b Hpopa Hpopb Hin. apply elem_of_cons in Hin.
            destruct Hin as [Heq'|Hrest].
            + pose proof (f_equal fst Heq') as Ha. simpl in Ha.
              pose proof (f_equal snd Heq') as Hb. simpl in Hb.
              subst a b. right. left. exact Hrcd.
            + apply Htot; done.
          - exact Htrans.
          - exact Hirr.
          - exact Hanti.
          - exact Hpoponly. }
        (* Case 3: (d,c) ∈ r *)
        destruct (decide (r d c)) as [Hrdc|Hnrdc].
        { exists r, _.
          split; [exact Hsub|split; [|split; [|split; [|split]]]].
          - intros a b Hpopa Hpopb Hin. apply elem_of_cons in Hin.
            destruct Hin as [Heq'|Hrest].
            + pose proof (f_equal fst Heq') as Ha. simpl in Ha.
              pose proof (f_equal snd Heq') as Hb. simpl in Hb.
              subst a b. right. right. exact Hrdc.
            + apply Htot; done.
          - exact Htrans.
          - exact Hirr.
          - exact Hanti.
          - exact Hpoponly. }
        (* Case 4: Neither (c,d) nor (d,c) in r. Add (c,d) and take tc. *)
        assert (Hcd_dec : RelDecision (λ x y, (x = c ∧ y = d) ∨ r x y)).
        { intros x y. cbv beta. apply _. }
        exists (tc (λ x y, (x = c ∧ y = d) ∨ r x y)), _.
        split; [|split; [|split; [|split; [|split]]]].
        + (* w1_pop ⊆ tc (insert (c,d) r) *)
          intros x y Hw1pop.
          apply tc_once. right. apply Hsub. done.
        + (* Totality on (c,d) :: rest *)
          intros a b Hpopa Hpopb Hin. apply elem_of_cons in Hin.
          destruct Hin as [Heq'|Hrest].
          * (* a = c, b = d *)
            pose proof (f_equal fst Heq') as Ha. simpl in Ha.
            pose proof (f_equal snd Heq') as Hb. simpl in Hb.
            subst a b. right. left. apply tc_once. left. split; reflexivity.
          * (* In rest *)
            destruct (Htot a b Hpopa Hpopb Hrest) as [Heq|[Hrab|Hrba]].
            -- left. done.
            -- right. left. apply tc_once. right. done.
            -- right. right. apply tc_once. right. done.
        + (* Transitive: tc is always transitive *)
          exact tc_transitive.
        + (* Irreflexive *)
          apply help_irreflexive; [exact Htrans|exact Hirr|exact Hanti|exact Hnrcd|exact Hnrdc|exact Hneq].
        + (* Antisymmetric *)
          apply help_antisymmetric; [exact Htrans|exact Hirr|exact Hanti|exact Hnrcd|exact Hnrdc|exact Hneq].
        + (* Only pops *)
          intros a b Htcab.
          apply (r_is_pop_then_trancl_is_pop (λ x y, (x = c ∧ y = d) ∨ r x y) a b).
          * intros aa ba Hxy. eapply is_pop_preserved; [exact Hpopc|exact Hpopd|exact Hpoponly|exact Hxy].
          * done. }
    (* Now we need to build the list of all pairs from enum *)
    (* all_pairs enum = [(a,b) | a ∈ enum, b ∈ enum] *)
    set (all_pairs := flat_map (λ a, map (λ b, (a, b)) enum) enum).
    destruct (Hind all_pairs) as (r & Hr_dec & Hsub & Htot & Htrans & Hirr & Hanti & Hpoponly).
    exists r, _. unfold w2.
    split; [exact Hsub|split; [|split; [|split; [|split]]]].
    - (* Totality on pop_ops *)
      intros a b Hpopa Hpopb.
      (* Show (a,b) ∈ all_pairs *)
      apply (Htot a b Hpopa Hpopb).
      unfold all_pairs.
      apply list_elem_of_In, in_flat_map.
      exists a. split.
      + apply list_elem_of_In, Henum. done.
      + apply in_map_iff. exists b. split; [done|].
        apply list_elem_of_In, Henum. done.
    - exact Htrans.
    - exact Hirr.
    - exact Hanti.
    - exact Hpoponly.
  Qed.

  (* remove_relaxed_stack.thy:1183-1184 *)
  Lemma lem_w2_then_pop r : w2 r → ∀ a b, r a b → is_pop val a ∧ is_pop val b.
  Proof.
    intros (_ & _ & _ & _ & _ & Hpop). done.
  Qed.

  (* remove_relaxed_stack.thy:1186-1187 *)
  Lemma lem_w2_pop_total r a b : w2 r → is_pop val a → is_pop val b → a ≠ b → r a b ∨ r b a.
  Proof.
    intros (_ & Htotal & _) Hpopa Hpopb Hneq.
    destruct (Htotal a b Hpopa Hpopb) as [Heq|[Hab|Hba]].
    - done.
    - left. done.
    - right. done.
  Qed.

  (* remove_relaxed_stack.thy:1189-1190 *)
  Lemma lem_w2_antisymmetric r : w2 r → Antisymmetric operation (=) r.
  Proof.
    intros (_ & _ & _ & _ & Hanti & _). done.
  Qed.

  (* remove_relaxed_stack.thy:1192-1193 *)
  Lemma tc_fold_trans (r : relation operation) : Transitive r → ∀ x y, tc r x y → r x y.
  Proof.
    intros Htrans x y Htc.
    induction Htc as [a b Hab|a b c Hab Hbc IHbc].
    - exact Hab.
    - eapply Htrans; [exact Hab|exact IHbc].
  Qed.

  Lemma lem_w2_acyclic r : w2 r → Acyclic r.
  Proof.
    intros Hw2 x Htc.
    destruct Hw2 as (Hsub & Htotal & Htrans & Hirr & Hanti & Hpop).
    apply tc_fold_trans in Htc; [|exact Htrans].
    by eapply Hirr.
  Qed.

  (* remove_relaxed_stack.thy:1195-1196 *)
  Lemma lem_w2_transitive r : w2 r → Transitive r.
  Proof.
    intros (_ & _ & Htrans & _). done.
  Qed.

  (* remove_relaxed_stack.thy:1198-1199 *)
  Lemma lem_preUw2_then_push_or_pop1 r a b : w2 r → (pre ∪ r) a b → is_push val a ∨ is_pop val a.
  Proof.
    intros Hw2 [Hpre|Hr].
    - destruct (def_push_or_pop _ _ Hpre) as [[e [He|He]] _].
      + left. exists e. done.
      + right. exists e. done.
    - right. destruct (lem_w2_then_pop r Hw2 a b Hr) as [Hpopa _]. done.
  Qed.

  (* remove_relaxed_stack.thy:1201-1202 *)
  Lemma lem_preUw2_then_push_or_pop2 r a b : w2 r → (pre ∪ r) a b → is_push val b ∨ is_pop val b.
  Proof.
    intros Hw2 [Hpre|Hr].
    - destruct (def_push_or_pop _ _ Hpre) as [_ [e [He|He]]].
      + left. exists e. done.
      + right. exists e. done.
    - right. destruct (lem_w2_then_pop r Hw2 a b Hr) as [_ Hpopb]. done.
  Qed.

  (* Helper lemma moved before lem_pre_w2D_help to use in its proof *)
  (* remove_relaxed_stack.thy:1235-1239 *)
  Lemma lem_pre_w2D2_help r a b : w2 r → tc (pre ∪ r) a b →
    is_pop val a ∨ pre a b ∨
    (is_push val a ∧ (∃ c, is_pop val c ∧ pre a c ∧ tc (pre ∪ r) c b)).
  Proof.
    intros Hw2 Htc.
    induction Htc as [x y Hxy|x y z Hxy Hyz IHyz].
    - (* Base case: (pre ∪ r) x y *)
      destruct Hxy as [Hpre|Hr].
      + (* pre x y *)
        right. left. exact Hpre.
      + (* r x y: by lem_w2_then_pop, x is pop *)
        left. destruct (lem_w2_then_pop r Hw2 x y Hr) as [Hpopx _]. exact Hpopx.
    - (* Induction: (pre ∪ r) x y, tc y z *)
      (* IH: is_pop val y ∨ pre y z ∨ (is_push val y ∧ ∃ c, is_pop val c ∧ pre y c ∧ tc c z) *)
      destruct Hxy as [Hprexy|Hrxy].
      + (* pre x y *)
        destruct IHyz as [Hpopy|[Hpreyz|(Hpushy & c & Hpopc & Hpreyc & Htccz)]].
        * (* y is pop *)
          (* pre x y with y pop. What is x? *)
          destruct (def_push_or_pop x y Hprexy) as [[e [Hxe|Hex]] _].
          -- (* val x e: x is push *)
             right. right. split; [exists e; exact Hxe|].
             exists y. split; [exact Hpopy|split; [exact Hprexy|exact Hyz]].
          -- (* val e x: x is pop *)
             left. exists e. exact Hex.
        * (* pre y z: by transitivity with pre x y, pre x z *)
          right. left. by eapply wf_pre_transitive.
        * (* is_push y ∧ ∃ c, ... *)
          (* pre x y with y push. What is x? *)
          destruct (def_push_or_pop x y Hprexy) as [[e [Hxe|Hex]] _].
          -- (* val x e: x is push. pre x y, pre y c. By trans, pre x c. *)
             right. right. split; [exists e; exact Hxe|].
             exists c. split; [exact Hpopc|split; [|exact Htccz]].
             eapply wf_pre_transitive; [exact Hprexy|exact Hpreyc].
          -- (* val e x: x is pop *)
             left. exists e. exact Hex.
      + (* r x y: x is pop *)
        left. destruct (lem_w2_then_pop r Hw2 x y Hrxy) as [Hpopx _]. exact Hpopx.
  Qed.

  (* Combined helper for lem_pre_w2D_help. Proves three results simultaneously
     to get a stronger IH that covers all suffix paths. *)
  Lemma lem_pre_w2D_help_combined r z : w2 r →
    ∀ m, tc (pre ∪ r) m z →
    (* Result 1: the goal for m itself *)
    (is_push val m ∨ (is_pop val z ∧ r m z) ∨ pre m z ∨
     (∃ c, is_pop val c ∧ r m c ∧ pre c z)) ∧
    (* Result 2: pop mode - for any pop x' with r x' m when m is pop *)
    (is_pop val m → ∀ x', is_pop val x' → r x' m →
     is_push val x' ∨ (is_pop val z ∧ r x' z) ∨ pre x' z ∨
     (∃ c, is_pop val c ∧ r x' c ∧ pre c z)) ∧
    (* Result 3: push mode - for any pop x' with pre x' m when m is push *)
    (is_push val m → ∀ x', is_pop val x' → pre x' m →
     is_push val x' ∨ (is_pop val z ∧ r x' z) ∨ pre x' z ∨
     (∃ c, is_pop val c ∧ r x' c ∧ pre c z)).
  Proof.
    intros Hw2.
    pose proof Hw2 as Hw2'.
    destruct Hw2 as (Hsub & _ & Htrans & _ & _ & Hpoponly).
    induction 1 as [m1 z1 Hm1z1|m1 m2 z1 Hm1m2 Hm2z1 IH].
    - (* Base: (pre ∪ r) m z *)
      split; [|split].
      + (* Result 1 *)
        destruct Hm1z1 as [Hpre|Hr].
        * right. right. left. exact Hpre.
        * right. left. split; [|exact Hr].
          destruct (lem_w2_then_pop r Hw2' m1 z1 Hr) as [_ Hpopz]. exact Hpopz.
      + (* Result 2: is_pop m → ∀ x' pop, r x' m → goal *)
        intros Hpopm x' Hpopx' Hrx'm.
        destruct Hm1z1 as [Hpremz|Hrmz].
        * (* pre m z *)
          right. right. right.
          exists m1. split; [exact Hpopm|split; [exact Hrx'm|exact Hpremz]].
        * (* r m z *)
          assert (Hrx'z : r x' z1) by (eapply Htrans; [exact Hrx'm|exact Hrmz]).
          destruct (Hpoponly m1 z1 Hrmz) as [_ Hpopz].
          right. left. split; [exact Hpopz|exact Hrx'z].
      + (* Result 3: is_push m → ∀ x' pop, pre x' m → goal *)
        intros Hpushm x' Hpopx' Hprex'm.
        destruct Hm1z1 as [Hpremz|Hrmz].
        * (* pre m z *)
          right. right. left. eapply wf_pre_transitive; [exact Hprex'm|exact Hpremz].
        * (* r m z: impossible since m is push *)
          exfalso.
          destruct (lem_w2_then_pop r Hw2' m1 z1 Hrmz) as [Hpopm _].
          destruct Hpushm as [rm Hrm]. destruct Hpopm as [im Him].
          eapply def_val_order; [exact Hrm|exists im; left; done].
    - (* Step: (pre ∪ r) m1 m2, tc m2 z1 *)
      destruct IH as [IH1 [IH2 IH3]].
      split; [|split].
      + (* Result 1: goal for m1 and z1 *)
        destruct Hm1m2 as [Hprem1m2|Hrm1m2].
        * (* pre m1 m2 *)
          destruct IH1 as [Hpushm2|[(Hpopz & Hrm2z)|[Hprem2z|(c & Hpopc & Hrm2c & Hprecz)]]].
          -- (* m2 is push *)
             destruct (def_push_or_pop m1 m2 Hprem1m2) as [[e [Hm1e|Hem1]] _].
             ++ left. exists e. exact Hm1e.
             ++ (* m1 is pop, m2 is push: use Result 3 of IH *)
                assert (Hpopm1 : is_pop val m1) by (exists e; exact Hem1).
                specialize (IH3 Hpushm2 m1 Hpopm1 Hprem1m2).
                exact IH3.
          -- (* is_pop z ∧ r m2 z *)
             destruct (def_push_or_pop m1 m2 Hprem1m2) as [[e [Hm1e|Hem1]] _].
             ++ left. exists e. exact Hm1e.
             ++ (* m1 pop *)
                assert (Hpopm1 : is_pop val m1) by (exists e; exact Hem1).
                destruct (def_push_or_pop m1 m2 Hprem1m2) as [_ [e2 [Hm2e2|He2m2]]].
                ** (* m2 push: r m2 z means m2 pop - contradiction *)
                   destruct (Hpoponly m2 z1 Hrm2z) as [Hpopm2 _].
                   destruct Hpopm2 as [im2 Him2]. exfalso.
                   eapply def_val_order; [exact Hm2e2|exists im2; left; done].
                ** (* m2 pop *)
                   assert (Hpopm2 : is_pop val m2) by (exists e2; exact He2m2).
                   assert (Hw1m1m2 : w1 m1 m2) by (apply lem_pr_then_w1; done).
                   assert (Hw1popm1m2 : w1_pop m1 m2).
                   { unfold w1_pop. split; [exact Hpopm1|split; [exact Hpopm2|exact Hw1m1m2]]. }
                   assert (Hrm1m2' : r m1 m2) by (apply Hsub; exact Hw1popm1m2).
                   assert (Hrm1z : r m1 z1) by (eapply Htrans; [exact Hrm1m2'|exact Hrm2z]).
                   right. left. split; [exact Hpopz|exact Hrm1z].
          -- (* pre m2 z *)
             destruct (def_push_or_pop m1 m2 Hprem1m2) as [[e [Hm1e|Hem1]] _].
             ++ left. exists e. exact Hm1e.
             ++ right. right. left. eapply wf_pre_transitive; [exact Hprem1m2|exact Hprem2z].
          -- (* ∃ c, is_pop c ∧ r m2 c ∧ pre c z *)
             destruct (def_push_or_pop m1 m2 Hprem1m2) as [[e [Hm1e|Hem1]] _].
             ++ left. exists e. exact Hm1e.
             ++ (* m1 pop *)
                assert (Hpopm1 : is_pop val m1) by (exists e; exact Hem1).
                destruct (def_push_or_pop m1 m2 Hprem1m2) as [_ [e2 [Hm2e2|He2m2]]].
                ** (* m2 push: r m2 c means m2 pop - contradiction *)
                   destruct (Hpoponly m2 c Hrm2c) as [Hpopm2 _].
                   destruct Hpopm2 as [im2 Him2]. exfalso.
                   eapply def_val_order; [exact Hm2e2|exists im2; left; done].
                ** (* m2 pop *)
                   assert (Hpopm2 : is_pop val m2) by (exists e2; exact He2m2).
                   assert (Hw1m1m2 : w1 m1 m2) by (apply lem_pr_then_w1; done).
                   assert (Hw1popm1m2 : w1_pop m1 m2).
                   { unfold w1_pop. split; [exact Hpopm1|split; [exact Hpopm2|exact Hw1m1m2]]. }
                   assert (Hrm1m2' : r m1 m2) by (apply Hsub; exact Hw1popm1m2).
                   assert (Hrm1c : r m1 c) by (eapply Htrans; [exact Hrm1m2'|exact Hrm2c]).
                   right. right. right.
                   exists c. split; [exact Hpopc|split; [exact Hrm1c|exact Hprecz]].
        * (* r m1 m2 *)
          destruct (lem_w2_then_pop r Hw2' m1 m2 Hrm1m2) as [Hpopm1 Hpopm2].
          destruct IH1 as [Hpushm2|[(Hpopz & Hrm2z)|[Hprem2z|(c & Hpopc & Hrm2c & Hprecz)]]].
          -- (* m2 is push - contradicts m2 is pop *)
             destruct Hpushm2 as [rm2 Hrm2]. destruct Hpopm2 as [im2 Him2].
             exfalso. eapply def_val_order; [exact Hrm2|exists im2; left; done].
          -- (* r m2 z *)
             assert (Hrm1z : r m1 z1) by (eapply Htrans; [exact Hrm1m2|exact Hrm2z]).
             right. left. split; [exact Hpopz|exact Hrm1z].
          -- (* pre m2 z *)
             right. right. right.
             exists m2. split; [exact Hpopm2|split; [exact Hrm1m2|exact Hprem2z]].
          -- (* ∃ c *)
             assert (Hrm1c : r m1 c) by (eapply Htrans; [exact Hrm1m2|exact Hrm2c]).
             right. right. right.
             exists c. split; [exact Hpopc|split; [exact Hrm1c|exact Hprecz]].
      + (* Result 2: is_pop m1 → ∀ x' pop, r x' m1 → goal *)
        intros Hpopm1 x' Hpopx' Hrx'm1.
        destruct Hm1m2 as [Hprem1m2|Hrm1m2].
        * (* pre m1 m2 *)
          destruct (def_push_or_pop m1 m2 Hprem1m2) as [_ [e2 [Hm2e2|He2m2]]].
          -- (* m2 is push: use IH3 with x'' = m1 *)
             assert (Hpushm2 : is_push val m2) by (exists e2; exact Hm2e2).
             specialize (IH3 Hpushm2 m1 Hpopm1 Hprem1m2).
             destruct IH3 as [Hpushm1|[(Hpopz & Hrm1z)|[Hprem1z|(c & Hpopc & Hrm1c & Hprecz)]]].
             ++ (* is_push m1 - contradicts is_pop m1 *)
                destruct Hpushm1 as [rm1 Hrm1']. destruct Hpopm1 as [im1 Him1].
                exfalso. eapply def_val_order; [exact Hrm1'|exists im1; left; done].
             ++ (* r m1 z *)
                assert (Hrx'z : r x' z1) by (eapply Htrans; [exact Hrx'm1|exact Hrm1z]).
                right. left. split; [exact Hpopz|exact Hrx'z].
             ++ (* pre m1 z *)
                right. right. right.
                exists m1. split; [exact Hpopm1|split; [exact Hrx'm1|exact Hprem1z]].
             ++ (* ∃ c *)
                assert (Hrx'c : r x' c) by (eapply Htrans; [exact Hrx'm1|exact Hrm1c]).
                right. right. right.
                exists c. split; [exact Hpopc|split; [exact Hrx'c|exact Hprecz]].
          -- (* m2 is pop: use IH2 *)
             assert (Hpopm2 : is_pop val m2) by (exists e2; exact He2m2).
             assert (Hw1m1m2 : w1 m1 m2) by (apply lem_pr_then_w1; done).
             assert (Hw1popm1m2 : w1_pop m1 m2).
             { unfold w1_pop. split; [exact Hpopm1|split; [exact Hpopm2|exact Hw1m1m2]]. }
             assert (Hrm1m2' : r m1 m2) by (apply Hsub; exact Hw1popm1m2).
             assert (Hrx'm2 : r x' m2) by (eapply Htrans; [exact Hrx'm1|exact Hrm1m2']).
             specialize (IH2 Hpopm2 x' Hpopx' Hrx'm2).
             exact IH2.
        * (* r m1 m2: use IH2 *)
          assert (Hrx'm2 : r x' m2) by (eapply Htrans; [exact Hrx'm1|exact Hrm1m2]).
          destruct (lem_w2_then_pop r Hw2' m1 m2 Hrm1m2) as [_ Hpopm2].
          specialize (IH2 Hpopm2 x' Hpopx' Hrx'm2).
          exact IH2.
      + (* Result 3: is_push m1 → ∀ x' pop, pre x' m1 → goal *)
        intros Hpushm1 x' Hpopx' Hprex'm1.
        destruct Hm1m2 as [Hprem1m2|Hrm1m2].
        * (* pre m1 m2 *)
          assert (Hprex'm2 : pre x' m2) by (eapply wf_pre_transitive; [exact Hprex'm1|exact Hprem1m2]).
          destruct (def_push_or_pop m1 m2 Hprem1m2) as [_ [e2 [Hm2e2|He2m2]]].
          -- (* m2 is push: use IH3 *)
             assert (Hpushm2 : is_push val m2) by (exists e2; exact Hm2e2).
             specialize (IH3 Hpushm2 x' Hpopx' Hprex'm2).
             exact IH3.
          -- (* m2 is pop: x' pop, m2 pop, pre x' m2 gives r x' m2 *)
             assert (Hpopm2 : is_pop val m2) by (exists e2; exact He2m2).
             assert (Hw1x'm2 : w1 x' m2) by (apply lem_pr_then_w1; done).
             assert (Hw1popx'm2 : w1_pop x' m2).
             { unfold w1_pop. split; [exact Hpopx'|split; [exact Hpopm2|exact Hw1x'm2]]. }
             assert (Hrx'm2 : r x' m2) by (apply Hsub; exact Hw1popx'm2).
             specialize (IH2 Hpopm2 x' Hpopx' Hrx'm2).
             exact IH2.
        * (* r m1 m2: impossible since m1 is push *)
          exfalso.
          destruct (lem_w2_then_pop r Hw2' m1 m2 Hrm1m2) as [Hpopm1' _].
          destruct Hpushm1 as [rm1 Hrm1]. destruct Hpopm1' as [im1 Him1].
          eapply def_val_order; [exact Hrm1|exists im1; left; done].
  Qed.

  (* remove_relaxed_stack.thy:1204-1229 *)
  (* Note: Complex proof with many cases. The Isabelle version uses SMT. *)
  Lemma lem_pre_w2D_help r a b : w2 r → tc (pre ∪ r) a b →
    is_push val a ∨ (is_pop val b ∧ r a b) ∨ pre a b ∨
    (∃ c, is_pop val c ∧ r a c ∧ pre c b).
  Proof.
    intros Hw2 Htc.
    destruct (lem_pre_w2D_help_combined r b Hw2 a Htc) as [IH1 _].
    exact IH1.
  Qed.

  (* remove_relaxed_stack.thy:1232-1233 *)
  Lemma lem_pre_w2D r a b : w2 r → tc (pre ∪ r) a b → is_pop val a → is_push val b →
    pre a b ∨ (∃ c, is_pop val c ∧ r a c ∧ pre c b).
  Proof.
    intros Hw2 Htc Hpopa Hpushb.
    destruct (lem_pre_w2D_help r a b Hw2 Htc) as [Hpusha | [(Hpopb & Hrab) | [Hpreab | (c & Hpopc & Hrac & Hprecb)]]].
    - (* is_push a - contradicts is_pop a *)
      destruct Hpusha as [ra Hara]. destruct Hpopa as [ia Hia].
      exfalso. eapply def_val_order; [exact Hara|exists ia; left; done].
    - (* is_pop b ∧ r a b - contradicts is_push b *)
      destruct Hpopb as [ib Hib]. destruct Hpushb as [rb Hrb].
      exfalso. eapply def_val_order; [exact Hrb|exists ib; left; done].
    - (* pre a b *)
      left. exact Hpreab.
    - (* ∃ c, is_pop c ∧ r a c ∧ pre c b *)
      right. exists c. split; [exact Hpopc|split; [exact Hrac|exact Hprecb]].
  Qed.

  (* remove_relaxed_stack.thy:1241-1242 *)
  Lemma lem_pre_w2D2 r a b : w2 r → tc (pre ∪ r) a b → is_push val a →
    pre a b ∨ (∃ c, is_pop val c ∧ pre a c ∧ tc (pre ∪ r) c b).
  Proof.
    intros Hw2 Htc Hpusha.
    destruct (lem_pre_w2D2_help r a b Hw2 Htc) as [Hpopa|[Hpre|(Hpusha' & c & Hpopc & Hpreac & Htccb)]].
    - (* a is pop: contradicts a is push *)
      destruct Hpopa as [ra Hvara]. destruct Hpusha as [ra' Hvara'].
      exfalso. eapply def_val_order; [exact Hvara'|exists ra; left; done].
    - (* pre a b *)
      left. exact Hpre.
    - (* is_push a ∧ ∃ c, ... *)
      right. exists c. split; [exact Hpopc|split; [exact Hpreac|exact Htccb]].
  Qed.

  (* remove_relaxed_stack.thy:1245-1246 *)
  Lemma lem_tranclpreUw2_then_push_or_pop1 r a b : w2 r → tc (pre ∪ r) a b →
    is_push val a ∨ is_pop val a.
  Proof.
    intros Hw2 Htc.
    (* Extract the first step of tc *)
    induction Htc as [x y Hxy|x y z Hxy Hyz IHyz].
    - eapply lem_preUw2_then_push_or_pop1; [exact Hw2|exact Hxy].
    - eapply lem_preUw2_then_push_or_pop1; [exact Hw2|exact Hxy].
  Qed.

  (* remove_relaxed_stack.thy:1248-1249 *)
  Lemma lem_tranclpreUw2_then_push_or_pop2 r a b : w2 r → tc (pre ∪ r) a b →
    is_push val b ∨ is_pop val b.
  Proof.
    intros Hw2 Htc.
    (* Extract the last step of tc *)
    induction Htc as [x y Hxy|x y z Hxy Hyz IHyz].
    - eapply lem_preUw2_then_push_or_pop2; [exact Hw2|exact Hxy].
    - exact IHyz.
  Qed.

  (* remove_relaxed_stack.thy:1252-1291 *)
  (* This proof requires complex case analysis using lem_pre_w2D, lem_pre_w2D2, etc. *)
  Lemma lem_trancl_pre_w2D r a b : w2 r → tc (pre ∪ r) a b →
    is_push val a ∨ is_push val b ∨ r a b.
  Proof.
    intros Hw2 Htc.
    pose proof Hw2 as Hw2'.
    destruct Hw2 as (Hsub & _ & Htrans & _ & _ & Hpoponly).
    induction Htc as [x y Hxy|x y z Hxy Hyz IHyz].
    - (* Base: (pre ∪ r) a b *)
      destruct Hxy as [Hpre|Hr].
      + (* pre a b *)
        destruct (def_push_or_pop x y Hpre) as [[e [Hxe|Hex]] [e' [Hye'|He'y]]].
        * left. exists e. exact Hxe.
        * left. exists e. exact Hxe.
        * right. left. exists e'. exact Hye'.
        * (* Both pops: w1_pop gives r *)
          right. right.
          assert (Hpopx : is_pop val x) by (exists e; exact Hex).
          assert (Hpopy : is_pop val y) by (exists e'; exact He'y).
          assert (Hw1xy : w1 x y) by (apply lem_pr_then_w1; done).
          assert (Hw1popxy : w1_pop x y) by (apply w1_popI; done).
          apply Hsub. exact Hw1popxy.
      + (* r a b *)
        right. right. exact Hr.
    - (* Inductive: (pre ∪ r) a y, tc y b *)
      destruct Hxy as [Hpreay|Hray].
      + (* pre a y *)
        destruct (def_push_or_pop x y Hpreay) as [[e [Hxe|Hex]] _].
        * (* a is push *)
          left. exists e. exact Hxe.
        * (* a is pop *)
          assert (Hpopa : is_pop val x) by (exists e; exact Hex).
          destruct IHyz as [Hpushy|[Hpushb|Hryz]].
          -- (* y is push *)
             (* a is pop, y is push, pre a y, tc y b *)
             (* Use lem_pre_w2D to analyze tc y b *)
             destruct (lem_tranclpreUw2_then_push_or_pop2 r y z Hw2' Hyz) as [Hpushb|Hpopb].
             ++ right. left. exact Hpushb.
             ++ (* b is pop *)
                (* a is pop, y is push, z is pop, pre a y, tc y z *)
                (* Use lem_pre_w2D2 on tc y z (y is push) *)
                destruct (lem_pre_w2D2 r y z Hw2' Hyz Hpushy) as [Hpreyz|(c & Hpopc & Hpreyc & Htccz)].
                ** (* pre y z *)
                   right. right.
                   assert (Hpreaz : pre x z) by (eapply wf_pre_transitive; [exact Hpreay|exact Hpreyz]).
                   assert (Hw1az : w1 x z) by (apply lem_pr_then_w1; done).
                   assert (Hw1popaz : w1_pop x z) by (apply w1_popI; done).
                   apply Hsub. exact Hw1popaz.
                ** (* ∃ c pop, pre y c, tc c z *)
                   (* pre a y, pre y c gives pre a c *)
                   assert (Hpreac : pre x c) by (eapply wf_pre_transitive; [exact Hpreay|exact Hpreyc]).
                   (* a pop, c pop, pre a c gives r a c *)
                   assert (Hw1ac : w1 x c) by (apply lem_pr_then_w1; done).
                   assert (Hw1popac : w1_pop x c) by (apply w1_popI; done).
                   assert (Hrac : r x c) by (apply Hsub; exact Hw1popac).
                   (* Now analyze tc c z with c pop *)
                   destruct (lem_tranclpreUw2_then_push_or_pop2 r c z Hw2' Htccz) as [Hpushz|Hpopz].
                   +++ right. left. exact Hpushz.
                   +++ (* Both c and z are pops, tc c z *)
                       (* Use lem_pre_w2D_help on tc c z *)
                       destruct (lem_pre_w2D_help r c z Hw2' Htccz) as [Hpushc'|[(Hpopz' & Hrcz)|[Hprecz|(d & Hpopd & Hrcd & Hpredz)]]].
                       *** (* c is push - contradiction *)
                           destruct Hpushc' as [rc Hrc]. destruct Hpopc as [ic Hic].
                           exfalso. eapply def_val_order; [exact Hrc|exists ic; left; done].
                       *** (* r c z *)
                           right. right. eapply Htrans; [exact Hrac|exact Hrcz].
                       *** (* pre c z *)
                           right. right.
                           assert (Hw1cz : w1 c z) by (apply lem_pr_then_w1; done).
                           assert (Hw1popcz : w1_pop c z) by (apply w1_popI; done).
                           assert (Hrcz : r c z) by (apply Hsub; exact Hw1popcz).
                           eapply Htrans; [exact Hrac|exact Hrcz].
                       *** (* ∃ d pop, r c d, pre d z *)
                           right. right.
                           assert (Hw1dz : w1 d z) by (apply lem_pr_then_w1; done).
                           assert (Hw1popdz : w1_pop d z) by (apply w1_popI; done).
                           assert (Hrdz : r d z) by (apply Hsub; exact Hw1popdz).
                           assert (Hrad : r x d) by (eapply Htrans; [exact Hrac|exact Hrcd]).
                           eapply Htrans; [exact Hrad|exact Hrdz].
          -- (* b is push *)
             right. left. exact Hpushb.
          -- (* r y z *)
             (* a pop, pre a y, r y z *)
             (* y must be pop (from r y z) *)
             destruct (Hpoponly y z Hryz) as [Hpopy _].
             (* a pop, y pop, pre a y gives r a y *)
             assert (Hw1ay : w1 x y) by (apply lem_pr_then_w1; done).
             assert (Hw1popay : w1_pop x y) by (apply w1_popI; done).
             assert (Hray' : r x y) by (apply Hsub; exact Hw1popay).
             right. right. eapply Htrans; [exact Hray'|exact Hryz].
      + (* r a y *)
        destruct (Hpoponly x y Hray) as [Hpopa Hpopy].
        destruct IHyz as [Hpushy|[Hpushb|Hryz]].
        * (* y is push - contradiction with y is pop *)
          destruct Hpushy as [ry Hry]. destruct Hpopy as [iy Hiy].
          exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
        * (* b is push *)
          right. left. exact Hpushb.
        * (* r y z *)
          right. right. eapply Htrans; [exact Hray|exact Hryz].
  Qed.

  (* remove_relaxed_stack.thy:1293-1294 *)
  Lemma lem_w1_in_w2 r a b : w2 r → w1 a b → is_pop val a → is_pop val b → r a b.
  Proof.
    intros (Hsub & _) Hw1 Hpopa Hpopb.
    apply Hsub.
    apply w1_popI; done.
  Qed.

  (* remove_relaxed_stack.thy:1296-1306 *)
  Lemma lem_not_w1_then_same_ir r a b e : w2 r → is_pop val a → is_pop val b → r a b →
    ¬ w1 a b → ir e a → ir e b.
  Proof.
    intros Hw2 Hpopa Hpopb Hrab Hnw1 Hirea.
    destruct (decide (ir e b)) as [Hireb|Hnireb]; [done|].
    exfalso.
    assert (Hpushe : is_push val e) by (by apply (ir_push_and_pop4 e a)).
    assert (Hirbe : ir b e) by (by apply not_ir_push_pop_ir).
    assert (Hpopba : pop_ir b a).
    { apply (pop_irI _ _ e); done. }
    assert (Hw1ba : w1 b a) by (apply lem_pop_ir_then_w1; done).
    assert (Hrba : r b a) by (apply (lem_w1_in_w2 r); done).
    (* Now we have r a b and r b a, derive contradiction with acyclicity *)
    assert (Htc : tc r a a).
    { eapply tc_l; [exact Hrab|]. apply tc_once. exact Hrba. }
    eapply (lem_w2_acyclic r); [exact Hw2|exact Htc].
  Qed.

  (* remove_relaxed_stack.thy:1308-1309 *)
  Lemma lem_not_w1_then_same_ir2 r a b e : w2 r → is_pop val a → is_pop val b → r a b →
    ¬ w1 a b → ir a e → ir b e.
  Proof.
    intros Hw2 Hpopa Hpopb Hrab Hnw1 Hirae.
    (* From ir a e with a pop, e must be push *)
    assert (Hpushe : is_push val e) by (by apply (ir_push_and_pop3 a e)).
    (* Either ir e b or ir b e *)
    destruct (push_pop_ordered _ _ Hpushe Hpopb) as [Hireb|Hirbe].
    - (* Case ir e b: we have ir a e and ir e b, so pop_ir a b *)
      exfalso.
      assert (Hpopab : pop_ir a b) by (apply (pop_irI _ _ e); done).
      apply Hnw1. apply lem_pop_ir_then_w1. done.
    - (* Case ir b e: this is our goal *)
      exact Hirbe.
  Qed.

  (* remove_relaxed_stack.thy:1311-1312 *)
  Lemma lem_not_w1_then_same_ir3 r a b e : w2 r → is_pop val a → is_pop val b → r a b →
    ¬ w1 a b → ir b e → ir a e.
  Proof.
    intros Hw2 Hpopa Hpopb Hrab Hnw1 Hirbe.
    (* From ir b e with b pop, e must be push *)
    assert (Hpushe : is_push val e) by (by apply (ir_push_and_pop3 b e)).
    (* Either ir e a or ir a e *)
    destruct (push_pop_ordered _ _ Hpushe Hpopa) as [Hirea|Hirae].
    - (* Case ir e a: we have ir b e and ir e a, so pop_ir b a *)
      exfalso.
      assert (Hpopba : pop_ir b a) by (apply (pop_irI _ _ e); done).
      (* This gives w1 b a *)
      assert (Hw1ba : w1 b a) by (apply lem_pop_ir_then_w1; done).
      (* Now r a b and w1 b a. From w1 b a with both pops, get r b a. *)
      assert (Hrba : r b a).
      { apply (lem_w1_in_w2 r); [done|done|done|done]. }
      (* Now r a b and r b a with w2 r gives a cycle, contradiction *)
      assert (Htc : tc r a a).
      { eapply tc_l; [exact Hrab|]. apply tc_once. exact Hrba. }
      eapply (lem_w2_acyclic r); [exact Hw2|exact Htc].
    - (* Case ir a e: this is our goal *)
      exact Hirae.
  Qed.

  (* remove_relaxed_stack.thy:1314-1315 *)
  Lemma lem_pr_in_w2 r a b : w2 r → is_pop val a → is_pop val b → pre a b → r a b.
  Proof.
    intros Hw2 Hpopa Hpopb Hpre.
    apply (lem_w1_in_w2 r); [done| |done|done].
    apply lem_pr_then_w1. done.
  Qed.

  (* remove_relaxed_stack.thy:1317-1318 *)
  Lemma help_me' r a b c : w2 r → r a b → w1 a b ∨ (ir c a → ir c b).
  Proof.
    intros Hw2 Hrab.
    destruct (decide (w1 a b)) as [Hw1|Hnw1]; [left; done|right].
    intros Hirca.
    destruct (lem_w2_then_pop r Hw2 a b Hrab) as [Hpopa Hpopb].
    eapply (lem_not_w1_then_same_ir r a b c); done.
  Qed.

  (* remove_relaxed_stack.thy:1320-1364 *)
  Lemma lem_prUw2_then_w1Uir r a b : w2 r → tc (pre ∪ r) a b →
    (is_pop val a ∧ is_pop val b ∧ r a b) ∨ tc (w1 ∪ ir) a b.
  Proof.
    intros Hw2 Htc.
    pose proof Hw2 as Hw2'.
    destruct Hw2 as (Hsub & _ & Htrans & _ & _ & Hpoponly).
    induction Htc as [x y Hxy|x y z Hxy Hyz IHyz].
    - (* Base: (pre ∪ r) a b *)
      destruct Hxy as [Hpre|Hr].
      + (* pre a b *)
        destruct (def_push_or_pop x y Hpre) as [[e [Hxe|Hex]] [e' [Hye'|He'y]]].
        * (* a is push, b is push *)
          right. apply tc_once. left.
          apply lem_pr_then_w1. done.
        * (* a is push, b is pop *)
          right. apply tc_once. right.
          apply lem_push_pr_pop_then_ir; [exists e; exact Hxe|exists e'; exact He'y|exact Hpre].
        * (* a is pop, b is push *)
          right. apply tc_once. right.
          apply lem_pop_pr_push_then_ir; [exists e; exact Hex|exists e'; exact Hye'|exact Hpre].
        * (* a is pop, b is pop *)
          left.
          assert (Hpopx : is_pop val x) by (exists e; exact Hex).
          assert (Hpopy : is_pop val y) by (exists e'; exact He'y).
          assert (Hw1xy : w1 x y) by (apply lem_pr_then_w1; done).
          assert (Hw1popxy : w1_pop x y) by (apply w1_popI; done).
          assert (Hrxy : r x y) by (apply Hsub; exact Hw1popxy).
          split; [exact Hpopx|split; [exact Hpopy|exact Hrxy]].
      + (* r a b *)
        left.
        destruct (Hpoponly x y Hr) as [Hpopx Hpopy].
        split; [exact Hpopx|split; [exact Hpopy|exact Hr]].
    - (* Inductive: (pre ∪ r) a y, tc y b *)
      destruct IHyz as [(Hpopy & Hpopz & Hryz)|Htcw1ir].
      + (* IH: is_pop y ∧ is_pop b ∧ r y b *)
        destruct Hxy as [Hpreay|Hray].
        * (* pre a y *)
          destruct (def_push_or_pop x y Hpreay) as [[e [Hxe|Hex]] _].
          -- (* a is push *)
             (* push a, pop y, pop z, pre a y, r y z *)
             (* pre a y with a push, y pop: ir a y *)
             right.
             assert (Hpusha : is_push val x) by (exists e; exact Hxe).
             assert (Hiray : ir x y) by (apply lem_push_pr_pop_then_ir; done).
             (* We have ir a y and r y z with y, z pops *)
             (* Need tc (w1 ∪ ir) a z *)
             (* Check if w1 y z or not *)
             destruct (decide (w1 y z)) as [Hw1yz|Hnw1yz].
             ++ (* w1 y z: tc via ir a y, w1 y z *)
                eapply tc_l; [right; exact Hiray|].
                apply tc_once. left. exact Hw1yz.
             ++ (* ¬ w1 y z: derive ir a z from lem_not_w1_then_same_ir *)
                assert (Hiraz : ir x z).
                { eapply lem_not_w1_then_same_ir; [exact Hw2'|exact Hpopy|exact Hpopz|exact Hryz|exact Hnw1yz|exact Hiray]. }
                apply tc_once. right. exact Hiraz.
          -- (* a is pop *)
             assert (Hpopa : is_pop val x) by (exists e; exact Hex).
             (* pop a, pop y, pop z, pre a y, r y z *)
             (* pre a y with both pops: w1_pop a y, hence r a y *)
             assert (Hw1ay : w1 x y) by (apply lem_pr_then_w1; done).
             assert (Hw1popay : w1_pop x y) by (apply w1_popI; done).
             assert (Hray : r x y) by (apply Hsub; exact Hw1popay).
             (* r a y, r y z gives r a z *)
             assert (Hraz : r x z) by (eapply Htrans; [exact Hray|exact Hryz]).
             left. split; [exact Hpopa|split; [exact Hpopz|exact Hraz]].
        * (* r a y *)
          destruct (Hpoponly x y Hray) as [Hpopa _].
          (* pop a, pop y, pop z, r a y, r y z *)
          assert (Hraz : r x z) by (eapply Htrans; [exact Hray|exact Hryz]).
          left. split; [exact Hpopa|split; [exact Hpopz|exact Hraz]].
      + (* IH: tc (w1 ∪ ir) y b *)
        destruct Hxy as [Hpreay|Hray].
        * (* pre a y *)
          destruct (def_push_or_pop x y Hpreay) as [[e [Hxe|Hex]] [e' [Hye'|He'y]]].
          -- (* a is push, y is push *)
             right.
             assert (Hw1ay : w1 x y) by (apply lem_pr_then_w1; done).
             eapply tc_l; [left; exact Hw1ay|exact Htcw1ir].
          -- (* a is push, y is pop *)
             right.
             assert (Hpusha : is_push val x) by (exists e; exact Hxe).
             assert (Hpopy : is_pop val y) by (exists e'; exact He'y).
             assert (Hiray : ir x y) by (apply lem_push_pr_pop_then_ir; done).
             eapply tc_l; [right; exact Hiray|exact Htcw1ir].
          -- (* a is pop, y is push *)
             right.
             assert (Hpopa : is_pop val x) by (exists e; exact Hex).
             assert (Hpushy : is_push val y) by (exists e'; exact Hye').
             assert (Hirxy : ir x y) by (apply lem_pop_pr_push_then_ir; done).
             (* ir a y, tc (w1 ∪ ir) y z: chain through *)
             eapply tc_l; [right; exact Hirxy|exact Htcw1ir].
          -- (* a is pop, y is pop *)
             right.
             assert (Hw1ay : w1 x y) by (apply lem_pr_then_w1; done).
             eapply tc_l; [left; exact Hw1ay|exact Htcw1ir].
        * (* r a y *)
          destruct (Hpoponly x y Hray) as [Hpopa Hpopy].
          destruct (lem_tranclpreUw2_then_push_or_pop2 r y z Hw2' Hyz) as [Hpushz|Hpopz].
          -- (* z is push *)
             right.
             assert (Htcaz : tc (pre ∪ r) x z).
             { eapply tc_l; [right; exact Hray|exact Hyz]. }
             destruct (lem_pre_w2D r x z Hw2' Htcaz Hpopa Hpushz) as [Hpreaz|(c & Hpopc & Hrac & Hprecz)].
             ++ (* pre a z *)
                assert (Hw1az : w1 x z) by (apply lem_pr_then_w1; done).
                apply tc_once. left. exact Hw1az.
             ++ (* ∃ c pop, r a c, pre c z *)
                assert (Hw1cz : w1 c z) by (apply lem_pr_then_w1; done).
                destruct (decide (w1 x c)) as [Hw1ac|Hnw1ac].
                ** eapply tc_l; [left; exact Hw1ac|apply tc_once; left; exact Hw1cz].
                ** (* ¬ w1 x c: use lem_not_w1_then_same_ir3 *)
                   (* c pop, z push, pre c z → ir c z *)
                   assert (Hircz : ir c z) by (apply lem_pop_pr_push_then_ir; done).
                   (* r x c, ¬ w1 x c, ir c z → ir x z *)
                   assert (Hirxz : ir x z).
                   { eapply lem_not_w1_then_same_ir3; [exact Hw2'|exact Hpopa|exact Hpopc|exact Hrac|exact Hnw1ac|exact Hircz]. }
                   apply tc_once. right. exact Hirxz.
          -- (* z is pop *)
             (* a pop, y pop, z pop, r a y, tc (w1 ∪ ir) y z *)
             (* tc (w1 ∪ ir) y z with both pops gives w1 y z by lem_trancl_w1UnirD *)
             apply lem_trancl_w1UnirD in Htcw1ir.
             destruct Htcw1ir as [(Hpushy & _ & _)|[(Hpushy & _ & _)|[(_ & Hpushz & _)|(_ & Hpopz' & Hw1yz)]]].
             ++ (* y push - contradiction with y pop *)
                destruct Hpushy as [ry Hry]. destruct Hpopy as [iy Hiy].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; exact Hiy].
             ++ (* y push - contradiction with y pop *)
                destruct Hpushy as [ry Hry]. destruct Hpopy as [iy Hiy].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; exact Hiy].
             ++ (* z push - contradiction with z pop *)
                destruct Hpushz as [rz Hrz]. destruct Hpopz as [iz Hiz].
                exfalso. eapply def_val_order; [exact Hrz|exists iz; left; exact Hiz].
             ++ (* w1 y z: derive r y z, then r x z by transitivity *)
                assert (Hw1popyz : w1_pop y z) by (apply w1_popI; done).
                assert (Hryz : r y z) by (apply Hsub; exact Hw1popyz).
                assert (Hrxz : r x z) by (eapply Htrans; [exact Hray|exact Hryz]).
                left. split; [exact Hpopa|split; [exact Hpopz'|exact Hrxz]].
  Qed.

  (* remove_relaxed_stack.thy:1368-1369 *)
  Lemma lem_w3_irreflexive r : w2 r → Irreflexive (tc (pre ∪ r)).
  Proof.
    intros Hw2 x Htcxx.
    destruct (lem_prUw2_then_w1Uir r x x Hw2 Htcxx) as [(Hpopx & _ & Hrxx)|Htcw1ir].
    - (* r x x: contradicts irreflexivity of r *)
      destruct Hw2 as (_ & _ & _ & Hirr & _).
      eapply Hirr. exact Hrxx.
    - (* tc (w1 ∪ ir) x x: use acyclicity of w1 ∪ ir *)
      eapply lem_w1_ir_acyclic. exact Htcw1ir.
  Qed.

  (* remove_relaxed_stack.thy:1371-1372 *)
  Lemma lem_w3_antisymmetric r : w2 r → Antisymmetric operation (=) (tc (pre ∪ r)).
  Proof.
    intros Hw2 x y Hxy Hyx.
    assert (Hirr : Irreflexive (tc (pre ∪ r))) by (apply lem_w3_irreflexive; done).
    assert (Htcxx : tc (pre ∪ r) x x) by (eapply tc_transitive; [exact Hxy|exact Hyx]).
    exfalso. eapply Hirr. exact Htcxx.
  Qed.

  (* remove_relaxed_stack.thy:1374-1375 *)
  Lemma val_then_not_w3 r ia ra : w2 r → val ia ra → ¬ tc (pre ∪ r) ra ia.
  Proof.
    intros Hw2 Hval Htc.
    assert (Hirr : Irreflexive (tc (pre ∪ r))) by (apply lem_w3_irreflexive; done).
    assert (Hpre : pre ia ra) by (apply rrs_val_then_pr; done).
    assert (Htcii : tc (pre ∪ r) ia ia).
    { eapply tc_l; [left; exact Hpre|exact Htc]. }
    eapply Hirr. exact Htcii.
  Qed.

  (* remove_relaxed_stack.thy:1377-1388 *)
  Lemma lem_witness_wellformed r : w2 r → WellformedHistory (tc (pre ∪ r)) val.
  Proof.
    intros Hw2.
    constructor.
    - (* Transitive *) apply tc_transitive.
    - (* Antisymmetric *) apply lem_w3_antisymmetric; done.
    - (* Irreflexive *) apply lem_w3_irreflexive; done.
    - (* FinitePredicate *) apply operation_finite.
    - (* push_once *) apply def_push_once.
    - (* pop_once *) apply def_pop_once.
    - (* val_order *) apply def_val_order.
    - (* def_push_or_pop *)
      intros a b Htc.
      destruct (lem_tranclpreUw2_then_push_or_pop1 r a b Hw2 Htc) as [Hpusha|Hpopa].
      + split.
        * destruct Hpusha as [ra Hra]. exists ra. left. done.
        * destruct (lem_tranclpreUw2_then_push_or_pop2 r a b Hw2 Htc) as [Hpushb|Hpopb].
          -- destruct Hpushb as [rb Hrb]. exists rb. left. done.
          -- destruct Hpopb as [ib Hib]. exists ib. right. done.
      + split.
        * destruct Hpopa as [ia Hia]. exists ia. right. done.
        * destruct (lem_tranclpreUw2_then_push_or_pop2 r a b Hw2 Htc) as [Hpushb|Hpopb].
          -- destruct Hpushb as [rb Hrb]. exists rb. left. done.
          -- destruct Hpopb as [ib Hib]. exists ib. right. done.
    - (* val_then_not_pr *)
      intros ia ra Hval.
      apply val_then_not_w3; done.
  Qed.

  (* remove_relaxed_stack.thy:1390-1393 *)
  Lemma lem_help_push_or_pop r a b : w2 r → tc (tc (pre ∪ r) ∪ ir) a b →
    is_push val a ∨ is_pop val a.
  Proof.
    intros Hw2 Htc.
    induction Htc as [x y Hxy|x y z Hxy Hyz IHyz].
    - destruct Hxy as [Htcpr|Hir].
      + eapply lem_tranclpreUw2_then_push_or_pop1; [exact Hw2|exact Htcpr].
      + destruct (ir_push_and_pop _ _ Hir) as [[Hpush _]|[Hpop _]]; [left|right]; done.
    - destruct Hxy as [Htcpr|Hir].
      + eapply lem_tranclpreUw2_then_push_or_pop1; [exact Hw2|exact Htcpr].
      + destruct (ir_push_and_pop _ _ Hir) as [[Hpush _]|[Hpop _]]; [left|right]; done.
  Qed.

  (* remove_relaxed_stack.thy:1395-1427 *)
  Lemma lem_w3_acyclic_help r a b : w2 r → tc (tc (pre ∪ r) ∪ ir) a b →
    (is_pop val a ∧ is_pop val b ∧ r a b) ∨ tc (w1 ∪ ir) a b.
  Proof.
    intros Hw2 Htc.
    pose proof Hw2 as Hw2'.
    destruct Hw2 as (Hsub & _ & Htrans & _ & _ & Hpoponly).
    induction Htc as [x y Hxy|x y z Hxy Hyz IHyz].
    - (* Base: (tc (pre ∪ r) ∪ ir) x y *)
      destruct Hxy as [Htcpr|Hir].
      + (* tc (pre ∪ r) x y *)
        destruct (lem_prUw2_then_w1Uir r x y Hw2' Htcpr) as [(Hpopx & Hpopy & Hrxy)|Htcw1ir].
        * left. split; [exact Hpopx|split; [exact Hpopy|exact Hrxy]].
        * right. exact Htcw1ir.
      + (* ir x y *)
        right. apply tc_once. right. exact Hir.
    - (* Inductive: (tc (pre ∪ r) ∪ ir) x y, tc y z *)
      destruct IHyz as [(Hpopy & Hpopz & Hryz)|Htcw1ir].
      + (* IH: is_pop y ∧ is_pop z ∧ r y z *)
        destruct Hxy as [Htcpr|Hir].
        * (* tc (pre ∪ r) x y *)
          destruct (lem_trancl_pre_w2D r x y Hw2' Htcpr) as [Hpushx|[Hpushy|Hrxy]].
          -- (* x is push *)
             right.
             destruct (lem_prUw2_then_w1Uir r x y Hw2' Htcpr) as [(Hpopx' & _ & _)|Htcw1ir_xy].
             ++ (* x is pop - contradiction *)
                destruct Hpushx as [rx Hrx]. destruct Hpopx' as [ix Hix].
                exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
             ++ (* tc (w1 ∪ ir) x y *)
                (* We have tc (w1 ∪ ir) x y, y pop, z pop, r y z *)
                destruct (decide (w1 y z)) as [Hw1yz|Hnw1yz].
                ** eapply tc_r; [exact Htcw1ir_xy|left; exact Hw1yz].
                ** (* ¬ w1 y z but r y z: use lem_not_w1_then_same_ir *)
                   (* From tc (w1 ∪ ir) x y with x push, y pop: ir x y *)
                   apply lem_trancl_w1UnirD in Htcw1ir_xy.
                   destruct Htcw1ir_xy as [(_ & Hpushy & _)|[(Hpushx' & _ & Hirxy)|[(_ & Hpushy & _)|(Hpopx' & _ & _)]]].
                   --- (* y push - contradiction *)
                       destruct Hpushy as [ry Hry]. destruct Hpopy as [iy Hiy].
                       exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
                   --- (* ir x y: derive ir x z *)
                       assert (Hirxz : ir x z).
                       { eapply lem_not_w1_then_same_ir; [exact Hw2'|exact Hpopy|exact Hpopz|exact Hryz|exact Hnw1yz|exact Hirxy]. }
                       apply tc_once. right. exact Hirxz.
                   --- (* y push - contradiction *)
                       destruct Hpushy as [ry Hry]. destruct Hpopy as [iy Hiy].
                       exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
                   --- (* x pop - contradiction with x push *)
                       destruct Hpushx as [rx Hrx]. destruct Hpopx' as [ix Hix].
                       exfalso. eapply def_val_order; [exact Hrx|exists ix; left; done].
          -- (* y is push - contradiction with y is pop *)
             destruct Hpushy as [ry Hry]. destruct Hpopy as [iy Hiy].
             exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
          -- (* r x y *)
             destruct (Hpoponly x y Hrxy) as [Hpopx _].
             left.
             assert (Hrxz : r x z) by (eapply Htrans; [exact Hrxy|exact Hryz]).
             split; [exact Hpopx|split; [exact Hpopz|exact Hrxz]].
        * (* ir x y *)
          right.
          destruct (ir_push_and_pop x y Hir) as [[Hpushx Hpopy']|[Hpopx Hpushy]].
          -- (* x push, y pop - but we also have y pop from IH *)
             destruct (decide (w1 y z)) as [Hw1yz|Hnw1yz].
             ++ eapply tc_l; [right; exact Hir|apply tc_once; left; exact Hw1yz].
             ++ (* ¬ w1 y z but r y z, and ir x y *)
                (* Use lem_not_w1_then_same_ir *)
                assert (Hirxz : ir x z).
                { eapply lem_not_w1_then_same_ir; [exact Hw2'|exact Hpopy|exact Hpopz|exact Hryz|exact Hnw1yz|exact Hir]. }
                apply tc_once. right. exact Hirxz.
          -- (* x pop, y push - contradiction with y is pop *)
             destruct Hpushy as [ry Hry]. destruct Hpopy as [iy Hiy].
             exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
      + (* IH: tc (w1 ∪ ir) y z *)
        destruct Hxy as [Htcpr|Hir].
        * (* tc (pre ∪ r) x y *)
          destruct (lem_prUw2_then_w1Uir r x y Hw2' Htcpr) as [(Hpopx & Hpopy & Hrxy)|Htcw1ir_xy].
          -- (* r x y with both pops *)
             (* Analyze tc (w1 ∪ ir) y z to determine if z is push or pop *)
             apply lem_trancl_w1UnirD in Htcw1ir.
             destruct Htcw1ir as [(Hpushy & _ & _)|[(Hpushy & _ & _)|[(_ & Hpushz & Hiryz)|(Hpopy' & Hpopz & Hw1yz)]]].
             ++ (* y push - contradiction with y pop *)
                destruct Hpushy as [ry Hry]. destruct Hpopy as [iy Hiy].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
             ++ (* y push - contradiction with y pop *)
                destruct Hpushy as [ry Hry]. destruct Hpopy as [iy Hiy].
                exfalso. eapply def_val_order; [exact Hry|exists iy; left; done].
             ++ (* y pop, z push, ir y z: derive ir x z *)
                right.
                destruct (decide (w1 x y)) as [Hw1xy|Hnw1xy].
                ** (* w1 x y: chain w1 x y, ir y z *)
                   eapply tc_l; [left; exact Hw1xy|apply tc_once; right; exact Hiryz].
                ** (* ¬ w1 x y: use lem_not_w1_then_same_ir3 *)
                   assert (Hirxz : ir x z).
                   { eapply lem_not_w1_then_same_ir3; [exact Hw2'|exact Hpopx|exact Hpopy|exact Hrxy|exact Hnw1xy|exact Hiryz]. }
                   apply tc_once. right. exact Hirxz.
             ++ (* y pop, z pop, w1 y z: derive r y z, then r x z *)
                left.
                assert (Hw1popyz : w1_pop y z) by (apply w1_popI; done).
                assert (Hryz : r y z) by (apply Hsub; exact Hw1popyz).
                assert (Hrxz : r x z) by (eapply Htrans; [exact Hrxy|exact Hryz]).
                split; [exact Hpopx|split; [exact Hpopz|exact Hrxz]].
          -- (* tc (w1 ∪ ir) x y *)
             right. eapply tc_transitive; [exact Htcw1ir_xy|exact Htcw1ir].
        * (* ir x y *)
          right. eapply tc_l; [right; exact Hir|exact Htcw1ir].
  Qed.

  (* remove_relaxed_stack.thy:1429-1433 *)
  Lemma lem_w3_acyclic r : w2 r → Acyclic (tc (pre ∪ r) ∪ ir).
  Proof.
    intros Hw2 x Htcx.
    destruct (lem_w3_acyclic_help r x x Hw2 Htcx) as [(Hpopx & _ & Hrxx)|Htcw1ir].
    - (* r x x: contradicts irreflexivity of r *)
      destruct Hw2 as (_ & _ & _ & Hirr & _).
      eapply Hirr. exact Hrxx.
    - (* tc (w1 ∪ ir) x x: use acyclicity of w1 ∪ ir *)
      eapply lem_w1_ir_acyclic. exact Htcw1ir.
  Qed.

  (* remove_relaxed_stack.thy:1435-1436 *)
  Lemma lem_w3_pop_ordered r a b : w2 r → is_pop val a → is_pop val b → a ≠ b →
    tc (pre ∪ r) a b ∨ tc (pre ∪ r) b a.
  Proof.
    intros Hw2 Hpopa Hpopb Hneq.
    destruct (lem_w2_pop_total r a b Hw2 Hpopa Hpopb Hneq) as [Hab|Hba].
    - left. apply tc_once. right. done.
    - right. apply tc_once. right. done.
  Qed.

  (* remove_relaxed_stack.thy:1440-1441 *)
  Lemma lem_w3_then_ins r a b : w2 r → is_push val a → is_push val b → tc (pre ∪ r) a b → ins a b.
  Proof.
    intros Hw2 Hpusha Hpushb Htc.
    destruct (lem_pre_w2D2 r a b Hw2 Htc Hpusha) as [Hpreab|(c & Hpopc & Hpreac & Htccb)].
    - (* pre a b *)
      apply lem_pr_then_ins; done.
    - (* ∃ c pop, pre a c, tc (pre ∪ r) c b *)
      (* Need to derive ir c b from tc (pre ∪ r) c b with c pop, b push *)
      destruct (lem_prUw2_then_w1Uir r c b Hw2 Htccb) as [(Hpopc' & Hpopb & _)|Htcw1ir].
      + (* c pop, b pop - contradicts b is push *)
        destruct Hpopb as [rb Hrb]. destruct Hpushb as [rb' Hrb'].
        exfalso. eapply def_val_order; [exact Hrb'|exists rb; left; done].
      + (* tc (w1 ∪ ir) c b *)
        (* c pop, b push, so lem_trancl_w1UnirD gives ir c b *)
        apply lem_trancl_w1UnirD in Htcw1ir.
        destruct Htcw1ir as [(Hpushc & _ & _)|[(Hpushc & _ & _)|[(_ & _ & Hircb)|(Hpopc' & Hpopb & _)]]].
        * (* c push - contradiction *)
          destruct Hpushc as [rc Hrc]. destruct Hpopc as [ic Hic].
          exfalso. eapply def_val_order; [exact Hrc|exists ic; left; done].
        * (* c push - contradiction *)
          destruct Hpushc as [rc Hrc]. destruct Hpopc as [ic Hic].
          exfalso. eapply def_val_order; [exact Hrc|exists ic; left; done].
        * (* ir c b - use insI *)
          apply (insI _ _ c); done.
        * (* b pop - contradiction *)
          destruct Hpopb as [rb Hrb]. destruct Hpushb as [rb' Hrb'].
          exfalso. eapply def_val_order; [exact Hrb'|exists rb; left; done].
  Qed.

  (* remove_relaxed_stack.thy:1443-1464 *)
  Lemma lem_w3ins_then_ins r a b c : w2 r → is_push val a → is_push val b → is_pop val c →
    tc (pre ∪ r) a c → ir c b → ins a b.
  Proof.
    intros Hw2 Hpusha Hpushb Hpopc Htcac Hircb.
    destruct (lem_pre_w2D2 r a c Hw2 Htcac Hpusha) as [Hpreac|(ca & Hpopca & Hpreaca & Htccac)].
    - (* pre a c: insI a b c *)
      apply (insI _ _ c); done.
    - (* ∃ ca pop, pre a ca, tc (pre ∪ r) ca c *)
      (* Analyze tc (pre ∪ r) ca c *)
      destruct (lem_trancl_pre_w2D r ca c Hw2 Htccac) as [Hpushca|[Hpushc|Hrcac]].
      + (* ca push - contradiction with ca pop *)
        destruct Hpushca as [rca Hrca]. destruct Hpopca as [ica Hica].
        exfalso. eapply def_val_order; [exact Hrca|exists ica; left; done].
      + (* c push - contradiction with c pop *)
        destruct Hpushc as [rc Hrc]. destruct Hpopc as [ic Hic].
        exfalso. eapply def_val_order; [exact Hrc|exists ic; left; done].
      + (* r ca c: both ca and c are pops *)
        destruct (decide (w1 ca c)) as [Hw1cac|Hnw1cac].
        * (* w1 ca c: use push_pop_ordered on b push, ca pop *)
          destruct (push_pop_ordered b ca Hpushb Hpopca) as [Hirbca|Hircab].
          -- (* ir b ca: derive contradiction via cycle *)
             (* ir c b, ir b ca gives pop_ir c ca *)
             assert (Hpopircca : pop_ir c ca) by (apply (pop_irI _ _ b); done).
             (* pop_ir c ca gives w1 c ca *)
             assert (Hw1cca : w1 c ca) by (apply lem_pop_ir_then_w1; done).
             (* w1 c ca with both pops gives w1_pop c ca, hence r c ca *)
             assert (Hw1popcca : w1_pop c ca) by (apply w1_popI; done).
             assert (Hrcca : r c ca) by (destruct Hw2 as (Hsub & _); apply Hsub; done).
             (* But r ca c and r c ca contradicts acyclicity *)
             exfalso.
             assert (Htc : tc r ca ca).
             { eapply tc_l; [exact Hrcac|apply tc_once; exact Hrcca]. }
             eapply lem_w2_acyclic; [exact Hw2|exact Htc].
          -- (* ir ca b: insI a b ca *)
             apply (insI _ _ ca); done.
        * (* ¬ w1 ca c: use lem_not_w1_then_same_ir3 *)
          (* ir c b with r ca c, ¬ w1 ca c gives ir ca b *)
          assert (Hircab : ir ca b).
          { eapply lem_not_w1_then_same_ir3; [exact Hw2|exact Hpopca|exact Hpopc|exact Hrcac|exact Hnw1cac|exact Hircb]. }
          apply (insI _ _ ca); done.
  Qed.

  (* remove_relaxed_stack.thy:1466-1472 *)
  Lemma lem_wins_then_ins r a b : w2 r → ins_order (tc (pre ∪ r)) val ir a b → ins a b.
  Proof.
    intros Hw2 Hinsorder.
    unfold ins_order in Hinsorder.
    destruct Hinsorder as (Hpusha & Hpushb & [Htcab|(c & Htcac & Hircb)]).
    - (* tc (pre ∪ r) a b *)
      apply (lem_w3_then_ins r); done.
    - (* ∃ c, tc (pre ∪ r) a c ∧ ir c b *)
      (* c is pop since ir c b with b push *)
      assert (Hpopc : is_pop val c) by (apply (ir_push_and_pop2 _ _ Hircb); done).
      apply (lem_w3ins_then_ins r a b c); done.
  Qed.

  (* remove_relaxed_stack.thy:1474-1487 *)
  Lemma lem_w3_ooo r ia ra ib rb : w2 r →
    val ia ra → val ib rb →
    ins_order (tc (pre ∪ r)) val ir ia ib →
    ir ib ra → tc (pre ∪ r) rb ra.
  Proof.
    intros Hw2 Hvala Hvalb Hinsorder Hibirra.
    (* Get ins ia ib from lem_wins_then_ins *)
    assert (Hins : ins ia ib) by (apply (lem_wins_then_ins r); done).
    (* Construct lin rb ra from linI *)
    (* linI: val ib rb → val ia ra → ir ib ra → ins ia ib → lin rb ra *)
    assert (Hlin : lin rb ra) by (apply (linI ib rb ia ra); done).
    (* w1 rb ra from lem_lin_then_w1 *)
    assert (Hw1 : w1 rb ra) by (apply lem_lin_then_w1; done).
    (* ra and rb are pops *)
    assert (Hpopra : is_pop val ra) by (exists ia; done).
    assert (Hpoprb : is_pop val rb) by (exists ib; done).
    (* r rb ra from lem_w1_in_w2 *)
    assert (Hrrba : r rb ra) by (apply (lem_w1_in_w2 r); done).
    (* tc (pre ∪ r) rb ra *)
    apply tc_once. right. done.
  Qed.

  (* remove_relaxed_stack.thy:1489-1490 *)
  Lemma lem_pr_in_w3 r a b : w2 r → pre a b → tc (pre ∪ r) a b.
  Proof.
    intros _ Hpre. apply tc_once. left. done.
  Qed.

  (* remove_relaxed_stack.thy:1492-1510 *)
  Theorem remove_relaxed_stack_linearizable :
    ∃ prt (_ : RelDecision prt), subrelation pre prt ∧ InsertPrRelaxedStack prt val ir.
  Proof.
    destruct lem_exists_total_closure as (r & Hr_dec & Hw2).
    exists (tc (pre ∪ r)), _.
    split.
    - (* subrelation pre (tc (pre ∪ r)) *)
      intros a b Hpre. apply tc_once. left. done.
    - (* InsertPrRelaxedStack (tc (pre ∪ r)) val ir *)
      constructor.
      + (* WellformedHistory (tc (pre ∪ r)) val *)
        apply lem_witness_wellformed; done.
      + (* val_then_pr: val ia ra → tc (pre ∪ r) ia ra *)
        intros ia ra Hval.
        assert (Hpre : pre ia ra) by (apply rrs_val_then_pr; done).
        apply tc_once. left. done.
      + (* ipr_pop_ordered: is_pop a → is_pop b → a ≠ b → tc (pre ∪ r) a b ∨ tc (pre ∪ r) b a *)
        intros a b Hpopa Hpopb Hneq.
        apply lem_w3_pop_ordered; done.
      + (* ir_alternating *)
        apply rrs_ir_alternating.
      + (* pr_u_ir_acyclic: Acyclic (tc (pre ∪ r) ∪ ir) *)
        apply lem_w3_acyclic; done.
      + (* ipr_ooo *)
        intros ia ra ib rb Hvala Hvalb Hinsorder Hibirra.
        apply (lem_w3_ooo r ia ra ib rb); done.
  Qed.

End remove_relaxed_stack.

(* remove_relaxed_stack.thy:1514-1530 *)
Theorem remove_relaxed_stack_linearizable_final `{abstract_stack_model} pre val ir
    `{!RelDecision pre, !RelDecision val, !RelDecision ir} :
  RemoveRelaxedStack pre val ir → linearizable_non_empty_stack pre val.
Proof.
  intros Hrrs.
  (* Get prt1 with InsertPrRelaxedStack prt1 val ir *)
  destruct (remove_relaxed_stack_linearizable pre val ir) as (prt1 & Hprt1_dec & Hsub1 & Hipr).
  (* Get prt2 with InsertRelaxedStack prt2 val *)
  destruct (insert_pr_relaxed_stack_linearizable prt1 val ir) as (prt2 & Hprt2_dec & Hsub2 & Hir).
  (* Get prt3 with SequentialStack prt3 val *)
  destruct (insert_relaxed_stack_linearizable prt2 val) as (prt3 & Hprt3_dec & Hsub3 & Hseq).
  (* Construct linearizable_non_empty_stack *)
  unfold linearizable_non_empty_stack.
  split.
  - (* ConcHistory pre *)
    destruct Hrrs as [Hwf Habcd _ _ _ _ _].
    destruct Hwf.
    constructor; done.
  - (* ∃ prt, subrelation pre prt ∧ SequentialStack prt val *)
    exists prt3, _.
    split.
    + (* subrelation pre prt3 *)
      intros a b Hpre.
      apply Hsub3. apply Hsub2. apply Hsub1. done.
    + (* SequentialStack prt3 val *)
      exact Hseq.
Qed.
