From stdpp Require Import finite.
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect.bag.ext Require Import strict_partial_order_extension.
From iris_logatom.pure_logic.aspect.stack.ext Require Import conc_his_rel insert_relaxed_stack.

Local Instance relation_union {A} : Union (relation A) :=
  λ r1 r2, Relation_Operators.union A r1 r2.

Section insert_pr_relaxed_stack.
  Context `{abstract_stack_model}.
  Implicit Types (pre val : relation operation).

  (* insert_pr_relaxed_stack.thy:5-11 *)
  Class InsertPrRelaxedStack pre val ir := {
    #[local] ipr_stack_wellformed :: WellformedHistory pre val;
    val_then_pr ia ra : val ia ra → pre ia ra;
    ipr_pop_ordered a b : is_pop val a → is_pop val b → a ≠ b → pre a b ∨ pre b a;
    ir_alternating : alternating val ir;
    pr_u_ir_acyclic : Acyclic (pre ∪ ir);
    ipr_ooo ia ra ib rb : val ia ra → val ib rb → ins_order pre val ir ia ib → ir ib ra → pre rb ra;
  }.

  Context pre val ir `{!InsertPrRelaxedStack pre val ir}.
  Context `{!RelDecision pre, !RelDecision val}.

  (* Make parent class instances available *)
  #[local] Existing Instance ipr_stack_wellformed.
  #[local] Existing Instance wf_pre_transitive.
  #[local] Existing Instance wf_pre_antisymmetric.
  #[local] Existing Instance wf_pre_irreflexive.

  (* insert_pr_relaxed_stack.thy:16-17 *)
  Lemma push_pop_ordered a b : is_push val a → is_pop val b → ir a b ∨ ir b a.
  Proof.
    intros Hpush Hpop.
    apply (alternating_complete _ _ ir_alternating); done.
  Qed.

  (* insert_pr_relaxed_stack.thy:19-20 *)
  Lemma ir_push_and_pop a b : ir a b → (is_push val a ∧ is_pop val b) ∨ (is_pop val a ∧ is_push val b).
  Proof.
    intros Hir.
    apply (alternating_sound _ _ ir_alternating). done.
  Qed.

  (* insert_pr_relaxed_stack.thy:22-24 *)
  Definition ins : relation operation := ins_order pre val ir.

  (* insert_pr_relaxed_stack.thy:26-30 *)
  Lemma lem_pr_then_ins a b : is_push val a → is_push val b → pre a b → ins a b.
  Proof.
    intros Hpusha Hpushb Hpre.
    unfold ins, ins_order.
    split; [done|]. split; [done|]. left. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:32-33 *)
  Lemma insI a b c : is_push val a → is_push val b → pre a c → ir c b → ins a b.
  Proof.
    intros Hpusha Hpushb Hpre Hir.
    unfold ins, ins_order.
    split; [done|]. split; [done|]. right. exists c. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:35-36 *)
  Lemma ir_push_and_pop1 a b : ir a b → is_push val a → is_pop val b.
  Proof.
    intros Hir [ra Hval].
    destruct (ir_push_and_pop _ _ Hir) as [[_ Hpopb]|[Hpopa _]].
    - done.
    - exfalso. destruct Hpopa as [c Hca].
      eapply def_val_order; first exact Hval.
      exists c. left. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:38-39 *)
  Lemma ir_push_and_pop2 a b : ir a b → is_push val b → is_pop val a.
  Proof.
    intros Hir [rb Hval].
    destruct (ir_push_and_pop _ _ Hir) as [[_ Hpopb]|[Hpopa _]].
    - exfalso. destruct Hpopb as [c Hcb].
      eapply def_val_order; first exact Hval.
      exists c. left. done.
    - done.
  Qed.

  (* insert_pr_relaxed_stack.thy:41-42 *)
  Lemma ir_push_and_pop3 a b : ir a b → is_pop val a → is_push val b.
  Proof.
    intros Hir [c Hca].
    destruct (ir_push_and_pop _ _ Hir) as [[Hpusha _]|[_ Hpushb]].
    - exfalso. destruct Hpusha as [ra Hara].
      eapply def_val_order; first exact Hara.
      exists c. left. done.
    - done.
  Qed.

  (* insert_pr_relaxed_stack.thy:44-45 *)
  Lemma ir_push_and_pop4 a b : ir a b → is_pop val b → is_push val a.
  Proof.
    intros Hir [c Hcb].
    destruct (ir_push_and_pop _ _ Hir) as [[Hpusha _]|[_ Hpushb]].
    - done.
    - exfalso. destruct Hpushb as [rb Hbrb].
      eapply def_val_order; first exact Hbrb.
      exists c. left. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:47-59 *)
  Lemma lem_val_then_ir a b : val a b → ir a b.
  Proof.
    intros Hval.
    assert (Hpre : pre a b) by (by apply val_then_pr).
    assert (Hpusha : is_push val a) by (exists b; done).
    assert (Hpopb : is_pop val b) by (exists a; done).
    destruct (push_pop_ordered _ _ Hpusha Hpopb) as [Hir|Hirba].
    - done.
    - exfalso.
      assert (Htc_ba : tc (pre ∪ ir) b a) by (apply tc_once; right; done).
      assert (Htc_aa : tc (pre ∪ ir) a a) by (eapply tc_l; [left; exact Hpre|exact Htc_ba]).
      eapply pr_u_ir_acyclic. exact Htc_aa.
  Qed.

  (* insert_pr_relaxed_stack.thy:61-70 *)
  Lemma lem_push_pr_pop_then_ir a b : is_push val a → is_pop val b → pre a b → ir a b.
  Proof.
    intros Hpusha Hpopb Hpre.
    destruct (push_pop_ordered _ _ Hpusha Hpopb) as [Hir|Hirba].
    - done.
    - exfalso.
      assert (Htc_ba : tc (pre ∪ ir) b a) by (apply tc_once; right; done).
      assert (Htc_aa : tc (pre ∪ ir) a a) by (eapply tc_l; [left; exact Hpre|exact Htc_ba]).
      eapply pr_u_ir_acyclic. exact Htc_aa.
  Qed.

  (* insert_pr_relaxed_stack.thy:72-73 *)
  Lemma not_ir_push_pop_ir a b : ¬ ir a b → is_push val a → is_pop val b → ir b a.
  Proof.
    intros Hnir Hpusha Hpopb.
    destruct (push_pop_ordered _ _ Hpusha Hpopb) as [Hir|Hirba]; [done|done].
  Qed.

  (* insert_pr_relaxed_stack.thy:75-76 *)
  Lemma not_ir_pop_push_ir a b : ¬ ir a b → is_pop val a → is_push val b → ir b a.
  Proof.
    intros Hnir Hpopa Hpushb.
    destruct (push_pop_ordered _ _ Hpushb Hpopa) as [Hir|Hirba]; [done|done].
  Qed.

  (* insert_pr_relaxed_stack.thy:78-86 *)
  Lemma lem_pop_pr_push_then_ir a b : is_pop val a → is_push val b → pre a b → ir a b.
  Proof.
    intros Hpopa Hpushb Hpre.
    destruct (push_pop_ordered _ _ Hpushb Hpopa) as [Hirba|Hir].
    - exfalso.
      assert (Htc_ba : tc (pre ∪ ir) b a) by (apply tc_once; right; done).
      assert (Htc_aa : tc (pre ∪ ir) a a) by (eapply tc_l; [left; exact Hpre|exact Htc_ba]).
      eapply pr_u_ir_acyclic. exact Htc_aa.
    - done.
  Qed.

  (* Helper lemma *)
  Lemma lem_val_then_push_and_pop a b : val a b → is_push val a ∧ is_pop val b.
  Proof.
    intros Hval. split; [exists b|exists a]; done.
  Qed.

  (* insert_pr_relaxed_stack.thy:88-97 - inductive definition wir *)
  Inductive wir : relation operation :=
    | wir_intro a b : pre a b → is_push val a → is_pop val b → wir a b
    | wir_step a b ix rx ra :
        val ix rx → val a ra → is_pop val b →
        wir ix b → pre rx ra → pre b rx → wir a rx →
        wir a b.

  (* insert_pr_relaxed_stack.thy:100-115 *)
  Lemma lem_wir_pr_then_wir_help a b :
    wir a b → ∀ c, is_push val c ∨ ¬ pre b c ∨ (is_pop val c ∧ pre b c ∧ wir a c).
  Proof.
    intros Hwir. induction Hwir as [a b Hpre Hpush Hpop | a b ix rx ra H0 H1 H2 Hwir1 IHHwir1 H3 H4 Hwir2 IHHwir2].
    - (* wir_intro case *)
      intros c.
      destruct (decide (is_push val c)) as [Hpushc|Hnotpushc].
      + left. done.
      + destruct (decide (pre b c)) as [Hprebc|Hnotprebc].
        * right. right.
          assert (Hpopc : is_pop val c).
          { destruct (def_push_or_pop _ _ Hprebc) as [_ [e [He|He]]].
            - exfalso. apply Hnotpushc. exists e. done.
            - exists e. done. }
          split; [done|]. split; [done|].
          apply wir_intro; try done.
          by etrans.
        * right. left. done.
    - (* wir_step case *)
      intros c.
      destruct (decide (is_push val c)) as [Hpushc|Hnotpushc].
      + left. done.
      + destruct (decide (pre b c)) as [Hprebc|Hnotprebc].
        * right. right.
          assert (Hpopc : is_pop val c).
          { destruct (def_push_or_pop _ _ Hprebc) as [_ [e [He|He]]].
            - exfalso. apply Hnotpushc. exists e. done.
            - exists e. done. }
          split; [done|]. split; [done|].
          (* Need to show wir a c *)
          specialize (IHHwir1 c).
          destruct IHHwir1 as [Hpushc'|[Hnotprebc'|[_ [_ Hwirxc]]]].
          -- exfalso. apply Hnotpushc. done.
          -- exfalso. apply Hnotprebc'. done.
          -- (* Have wir ix c, need wir a c *)
             destruct (lem_val_then_push_and_pop _ _ H0) as [Hpushix Hpoprx].
             destruct (decide (c = rx)) as [->|Hneq].
             ++ exact Hwir2.
             ++ destruct (ipr_pop_ordered _ _ Hpopc Hpoprx Hneq) as [Hcrx|Hrxc].
                ** apply (wir_step _ _ ix rx ra); try done.
                ** specialize (IHHwir2 c).
                   destruct IHHwir2 as [Hpushc''|[Hnotrxc|[_ [_ Hwirac]]]].
                   --- exfalso. apply Hnotpushc. done.
                   --- exfalso. apply Hnotrxc. done.
                   --- done.
        * right. left. done.
  Qed.

  Lemma lem_wir_pr_then_wir a b c : wir a b → is_pop val c → pre b c → wir a c.
  Proof.
    intros Hwir Hpopc Hprebc.
    specialize (lem_wir_pr_then_wir_help _ _ Hwir c).
    intros [Hpushc|[Hnotprebc|[_ [_ Hwirac]]]].
    - exfalso. destruct Hpushc as [rc Hcrc].
      destruct Hpopc as [ic Hicc].
      eapply def_val_order; first exact Hcrc.
      exists ic. left. done.
    - exfalso. apply Hnotprebc. done.
    - done.
  Qed.

  (* insert_pr_relaxed_stack.thy:118-120 *)
  Lemma wir_right_rec ix rx a ra b :
    val ix rx → val a ra → is_pop val b →
    pre ix b → pre rx ra → wir a rx → wir a b.
  Proof.
    intros Hvalx Hvala Hpopb Hprixb Hprxra Hwirax.
    destruct (lem_val_then_push_and_pop _ _ Hvalx) as [Hpushix Hpoprx].
    destruct (decide (rx = b)) as [->|Hneq].
    - exact Hwirax.
    - destruct (ipr_pop_ordered _ _ Hpoprx Hpopb Hneq) as [Hrxb|Hbrx].
      + by apply (lem_wir_pr_then_wir _ rx).
      + assert (Hwirxb : wir ix b) by (apply wir_intro; done).
        apply (wir_step _ _ ix rx ra); done.
  Qed.

  (* insert_pr_relaxed_stack.thy:122-124 *)
  Lemma wir_left_rec ix rx a ra b :
    val ix rx → val a ra → is_pop val b →
    wir ix b → pre rx ra → pre a rx → wir a b.
  Proof.
    intros Hvalx Hvala Hpopb Hwirxb Hprxra Hprax.
    destruct (lem_val_then_push_and_pop _ _ Hvalx) as [Hpushix Hpoprx].
    destruct (lem_val_then_push_and_pop _ _ Hvala) as [Hpusha Hpopra].
    destruct (decide (rx = b)) as [->|Hneq].
    - apply wir_intro; done.
    - destruct (ipr_pop_ordered _ _ Hpoprx Hpopb Hneq) as [Hrxb|Hbrx].
      + apply wir_intro; try done.
        by etrans.
      + assert (Hwirarx : wir a rx) by (apply wir_intro; done).
        apply (wir_step _ _ ix rx ra); done.
  Qed.

  (* insert_pr_relaxed_stack.thy:126-127 *)
  Lemma wir_left_right_rec ix rx a ra b :
    val ix rx → val a ra → is_pop val b →
    wir ix b → pre rx ra → wir a rx → wir a b.
  Proof.
    intros Hvalx Hvala Hpopb Hwirxb Hprxra Hwirax.
    destruct (lem_val_then_push_and_pop _ _ Hvalx) as [Hpushix Hpoprx].
    destruct (decide (rx = b)) as [->|Hneq].
    - exact Hwirax.
    - destruct (ipr_pop_ordered _ _ Hpoprx Hpopb Hneq) as [Hrxb|Hbrx].
      + by apply (lem_wir_pr_then_wir _ rx).
      + apply (wir_step _ _ ix rx ra); done.
  Qed.

  (* insert_pr_relaxed_stack.thy:130-138 *)
  Lemma wirD ia rb :
    wir ia rb → pre ia rb ∨
      (∃ ix rx ra, val ix rx ∧ val ia ra ∧ is_pop val rb ∧
        wir ix rb ∧ pre rx ra ∧ pre rb rx ∧ wir ia rx).
  Proof.
    intros Hwir.
    destruct Hwir as [a b Hpre Hpusha Hpopb|a b ix rx ra Hvalx Hvala Hpopb Hwirxb Hprxra Hbrx Hwirax].
    - left. done.
    - right. exists ix, rx, ra. repeat split; done.
  Qed.

  (* insert_pr_relaxed_stack.thy:140-149 - inductive definition lwir *)
  Inductive lwir : relation operation :=
    | lwir_intro a b : pre a b → is_push val a → is_pop val b → lwir a b
    | lwir_step a b ix rx ra :
        val ix rx → val a ra → is_pop val b →
        lwir ix b → pre rx ra → pre b rx → pre a rx →
        lwir a b.

  (* insert_pr_relaxed_stack.thy:151-154 *)
  Lemma lem_lwir_then_wir a b : lwir a b → wir a b.
  Proof.
    intros Hlwir.
    induction Hlwir as [a b H0 H1 H2 | a b ix rx ra H0 H1 H2 Hlwir1 IHHlwir H3 H4 H5].
    - by apply wir_intro.
    - apply (wir_left_rec ix rx _ ra); try done.
  Qed.

  (* insert_pr_relaxed_stack.thy:156-160 *)
  Lemma lem_lwir_left_grow ia ra ib rb ic rc :
    lwir ib rc →
    val ia ra → val ib rb → val ic rc →
    pre rc rb → pre rb ra → pre ia rb →
    lwir ia rc.
  Proof.
    intros Hlwir Hvala Hvalb Hvalc Hprrcrb Hprrbra Hpriarb.
    destruct (lem_val_then_push_and_pop _ _ Hvalc) as [_ Hpoprc].
    apply (lwir_step _ _ ib rb ra); try done.
  Qed.

  (* insert_pr_relaxed_stack.thy:162-167 *)
  Lemma lem_lwir_trans ia rb ic rc :
    lwir ia rb →
    ∀ ra' ib', val ic rc → val ia ra' → val ib' rb →
    lwir ib' rc → pre rc rb → pre rb ra' →
    lwir ia rc.
  Proof.
    intros Hlwir. induction Hlwir as [a b H0 H1 H2 | a b ix rx ra H0 H1 H2 Hlwir1 IHHlwir H3 H4 H5].
    { (* lwir_intro case *)
      intros ra' ib' Hvalc Hvala' Hvalb' Hlwibrc Hprrcrb Hprrbra'.
      eapply lem_lwir_left_grow; done. }
    { (* lwir_step case *)
      intros ra' ib' Hvalc Hvala' Hvalb' Hlwibrc Hprrcrb Hprrbra'.
      assert (ra' = ra) by (eapply def_pop_once; eauto). subst ra'.
      (* First use IH to get lwir ix rc *)
      assert (Hwirxrc : lwir ix rc).
      { eapply IHHlwir; try done. }
      (* Now grow from ix to a using lem_lwir_left_grow *)
      eapply (lem_lwir_left_grow _ ra _ rx); try done.
      by etrans. }
  Qed.

  (* insert_pr_relaxed_stack.thy:169-172 *)
  Lemma lem_wir_then_lwir a b : wir a b → lwir a b.
  Proof.
    intros Hwir. induction Hwir as [a b H0 H1 H2 | a b ix rx ra H0 H1 H2 Hwir1 IHHwir1 H3 H4 Hwir2 IHHwir2].
    - by apply lwir_intro.
    - (* wir_step case *)
      destruct H2 as [ib Hibb].
      eapply (lem_lwir_trans _ rx _ b); done.
  Qed.

  (* insert_pr_relaxed_stack.thy:174-183 - inductive definition rwir *)
  Inductive rwir : relation operation :=
    | rwir_intro a b : pre a b → is_push val a → is_pop val b → rwir a b
    | rwir_step a b ix rx ra :
        val ix rx → val a ra → is_pop val b →
        pre ix b → pre rx ra → pre b rx → rwir a rx →
        rwir a b.

  (* insert_pr_relaxed_stack.thy:185-188 *)
  Lemma lem_rwir_then_wir a b : rwir a b → wir a b.
  Proof.
    intros Hrwir. induction Hrwir as [a b H0 H1 H2 | a b ix rx ra H0 H1 H2 H3 H4 H5 Hrwir1 IHHrwir].
    - by apply wir_intro.
    - apply (wir_right_rec ix rx _ ra); try done.
  Qed.

  (* insert_pr_relaxed_stack.thy:192-194 *)
  Lemma lem_left_grow ia ra ib rb ic rc :
    val ia ra → val ib rb → val ic rc →
    wir ia rb → pre ic ra → pre ra rc → wir ic rb.
  Proof.
    intros Hvala Hvalb Hvalc Hwir Hpricra Hprarc.
    destruct (lem_val_then_push_and_pop _ _ Hvalb) as [_ Hpoprb].
    apply (wir_left_rec ia ra _ rc); done.
  Qed.

  (* insert_pr_relaxed_stack.thy:196-198 *)
  Lemma lem_right_grow ia ra ib rb ic rc :
    val ia ra → val ib rb → val ic rc →
    pre rb ra → wir ia rb → pre ib rc → pre rc rb → wir ia rc.
  Proof.
    intros Hvala Hvalb Hvalc Hprrba Hwir Hpribc Hprrcb.
    destruct (lem_val_then_push_and_pop _ _ Hvalc) as [Hpushic Hpoprc].
    apply (wir_right_rec ib rb _ ra); done.
  Qed.

  (* insert_pr_relaxed_stack.thy:200-202 *)
  Lemma lem_rwir_right_grow ia ra ib rb ic rc :
    val ia ra → val ib rb → val ic rc →
    pre rc rb → rwir ia rb → pre ib rc → pre rb ra → rwir ia rc.
  Proof.
    intros Hvala Hvalb Hvalc Hprrcb Hrwir Hpribc Hprrba.
    destruct (lem_val_then_push_and_pop _ _ Hvalc) as [Hpushic Hpoprc].
    apply (rwir_step _ _ ib rb ra); done.
  Qed.

  (* insert_pr_relaxed_stack.thy:204-221 *)
  Lemma lem_rwir_left_grow ia ra ib rb ic rc :
    rwir ib rc →
    val ia ra → val ib rb → val ic rc →
    pre rc rb → pre rb ra → pre ia rb →
    rwir ia rc.
  Proof.
    intros Hrwir.
    revert ia ra rb ic.
    induction Hrwir as [ib' rc' Hpribrc Hpushib Hpoprc |
                        ib' rc' ix rx ra' Hvalix Hvalib Hpoprc Hprixrc Hprrxra Hprrcrx Hrwibrx IH].
    - (* Base case: rwir_intro *)
      intros ia ra rb ic Hvala Hvalb Hvalc Hprrcb Hprrba Hpriarb.
      (* First build rwir ia rb using rwir_intro *)
      assert (Hrwiriarb : rwir ia rb).
      { apply rwir_intro; try done.
        - destruct (lem_val_then_push_and_pop _ _ Hvala) as [? _]. done.
        - destruct (lem_val_then_push_and_pop _ _ Hvalb) as [_ ?]. done. }
      (* Now use rwir_step to extend to rwir ia rc' *)
      destruct (lem_val_then_push_and_pop _ _ Hvalc) as [_ Hpoprc'].
      eapply (rwir_step _ _ ib' rb ra); done.
    - (* Inductive case: rwir_step *)
      intros ia ra rb ic Hvala Hvalb Hvalc Hprrcb Hprrba Hpriarb.
      assert (ra' = rb) by (eapply def_pop_once; eauto). subst ra'.
      (* First use IH to get rwir ia rx *)
      assert (Hrwiriarx : rwir ia rx).
      { eapply IH; done. }
      (* Then use lem_rwir_right_grow to extend to rwir ia rc' *)
      eapply (lem_rwir_right_grow _ ra ix rx ic); try done.
      by etrans.
  Qed.

  (* insert_pr_relaxed_stack.thy:223-231 *)
  Lemma lem_rwir ia rb :
    rwir ia rb → pre ia rb ∨
      (∃ ix rx ra, val ix rx ∧ val ia ra ∧ is_pop val rb ∧
        pre ix rb ∧ pre rx ra ∧ pre rb rx ∧ rwir ia rx).
  Proof.
    intros Hrwir.
    destruct Hrwir as [a b Hpre Hpush Hpop | a b ix rx ra Hvalix Hvala Hpopb Hprixb Hprrxra Hprbx Hrwir'].
    - left. done.
    - right. exists ix, rx, ra. repeat split; done.
  Qed.

  (* insert_pr_relaxed_stack.thy:233-239 *)
  Lemma lem_rwir_trans ia ra ib rb ic rc :
    rwir ib rc →
    val ia ra → val ib rb → val ic rc →
    rwir ia rb → pre rb ra → pre rc rb →
    rwir ia rc.
  Proof.
    intros Hrwir.
    revert ia ra rb ic.
    induction Hrwir as [ib' rc' Hpribrc Hpushib Hpoprc |
                        ib' rc' ix rx ra' Hvalix Hvalib Hpoprc Hprixrc Hprrxra Hprrcrx Hrwibrx IH].
    { intros ia ra rb ic Hvala Hvalb Hvalc Hrwiriarb Hprrba Hprrcb.
      eapply (lem_rwir_right_grow _ ra ib' rb ic); done. }
    { intros ia ra rb ic Hvala Hvalb Hvalc Hrwiriarb Hprrba Hprrcb.
      assert (ra' = rb) by (eapply def_pop_once; eauto). subst ra'.
      (* Use IH to get rwir ia rx, then lem_rwir_right_grow to extend to rwir ia rc' *)
      assert (Hrwiriarx : rwir ia rx).
      { eapply IH; done. }
      eapply (lem_rwir_right_grow _ ra ix rx ic); try done.
      by etrans. }
  Qed.

  (* insert_pr_relaxed_stack.thy:241-244 *)
  Lemma lem_wir_then_rwir a b : wir a b → rwir a b.
  Proof.
    intros Hwir. induction Hwir as [a b H0 H1 H2 | a b ix rx ra H0 H1 H2 Hwir1 IHHwir1 H3 H4 Hwir2 IHHwir2].
    - by apply rwir_intro.
    - destruct H2 as [ib Hibb].
      eapply (lem_rwir_trans _ ra _ rx); done.
  Qed.

  (* insert_pr_relaxed_stack.thy:246-247 *)
  Lemma lem_rwir_then_push_and_pop a b : rwir a b → is_push val a ∧ is_pop val b.
  Proof.
    intros Hrwir. destruct Hrwir as [? ? Hpre Hpush Hpop |
                                      ? ? ix rx ra Hvalix Hvala Hpop Hprixb Hprrxra Hprbx Hrwir]; split.
    - done.
    - done.
    - destruct (lem_val_then_push_and_pop _ _ Hvala) as [? _]. done.
    - done.
  Qed.

  (* [rwir a] is reachability from the base pairs of [rwir_intro] along [rwir_step]. *)
  Local Definition rwir_base a b : Prop := pre a b ∧ is_push val a ∧ is_pop val b.
  Local Definition rwir_succ a rx b : Prop :=
    ∃ ix ra, val ix rx ∧ val a ra ∧ is_pop val b ∧ pre ix b ∧ pre rx ra ∧ pre b rx.

  Local Lemma rwir_reach a b :
    rwir a b ↔ rwir_base a b ∨ ∃ b0, rwir_base a b0 ∧ tc (rwir_succ a) b0 b.
  Proof.
    split.
    - induction 1 as [a b Hpre Hpush Hpop|a b ix rx ra Hvalix Hvala Hpop Hprixb Hprrxra Hprbrx _ IH].
      + by left.
      + right. assert (Hsucc : rwir_succ a rx b) by (exists ix, ra; done).
        destruct IH as [Hbase|(b0 & Hbase & Hb0rx)].
        * exists rx. split; [done|by apply tc_once].
        * exists b0. split; [done|by eapply tc_r].
    - intros [(Hpre & Hpush & Hpop)|(b0 & (Hpre & Hpush & Hpop) & Hb0b)];
        first by apply rwir_intro.
      assert (Hb0 : rwir a b0) by by apply rwir_intro.
      clear Hpre Hpush Hpop. revert Hb0.
      induction Hb0b as [b0 b Hsucc|b0 c b Hsucc _ IH]; intros Hb0;
        destruct Hsucc as (ix & ra & ? & ? & ? & ? & ? & ?).
      + by apply (rwir_step _ _ ix b0 ra).
      + apply IH. by apply (rwir_step _ _ ix b0 ra).
  Qed.

  Local Instance rwir_base_dec : RelDecision rwir_base.
  Proof. intros a b. unfold rwir_base, is_push, is_pop. apply _. Qed.

  Local Instance rwir_succ_dec a : RelDecision (rwir_succ a).
  Proof. intros rx b. unfold rwir_succ, is_pop. apply _. Qed.

  Local Instance wir_dec : RelDecision wir.
  Proof.
    intros a b.
    destruct (decide (rwir_base a b ∨ ∃ b0, rwir_base a b0 ∧ tc (rwir_succ a) b0 b))
      as [Hr|Hnr].
    - left. by apply lem_rwir_then_wir, rwir_reach.
    - right. intros Hwir. by apply Hnr, rwir_reach, lem_wir_then_rwir.
  Qed.

  (* insert_pr_relaxed_stack.thy:250-252 *)
  Definition wri : relation operation :=
    λ a b, is_pop val a ∧ is_push val b ∧ ¬ wir b a.

  (* insert_pr_relaxed_stack.thy:254-256 *)
  Definition wii : relation operation :=
    λ a b, is_push val a ∧ is_push val b ∧ pre a b.

  (* insert_pr_relaxed_stack.thy:258-260 *)
  Definition wrr : relation operation :=
    λ a b, is_pop val a ∧ is_pop val b ∧ pre a b.

  (* insert_pr_relaxed_stack.thy:262-264 *)
  Definition pr_witness : relation operation :=
    tc (wir ∪ wri ∪ wii ∪ wrr).

  (* insert_pr_relaxed_stack.thy:266-267 *)
  Lemma lem_wir_then_push_and_pop a b : wir a b → is_push val a ∧ is_pop val b.
  Proof.
    intros Hwir. destruct Hwir as [? ? Hpre Hpush Hpop |
                                    ? ? ix rx ra Hvalix Hvala Hpop Hwir1 Hprrxra Hprbx Hwir2]; split.
    - done.
    - done.
    - destruct (lem_val_then_push_and_pop _ _ Hvala) as [? _]. done.
    - done.
  Qed.

  (* insert_pr_relaxed_stack.thy:269-270 *)
  Lemma lem_wri_then_pop_and_push a b : wri a b → is_pop val a ∧ is_push val b.
  Proof.
    intros [Hpopa [Hpushb _]]. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:272-278 *)
  Lemma lem_wir_wri_total a b : is_push val a → is_pop val b → wir a b ∨ wri b a.
  Proof.
    intros Hpusha Hpopb.
    destruct (decide (wir a b)) as [Hwir | Hnwir].
    - left. done.
    - right. unfold wri. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:280-286 *)
  Lemma lem_wrr_total a b : is_pop val a → is_pop val b → a ≠ b → wrr a b ∨ wrr b a.
  Proof.
    intros Hpopa Hpopb Hne.
    unfold wrr.
    destruct (ipr_pop_ordered a b Hpopa Hpopb Hne) as [Hpre | Hpre].
    - left. done.
    - right. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:288-291 *)
  Lemma lem_wir_then_not_wri a b : is_push val a → is_pop val b → wir a b → ¬ wri b a.
  Proof.
    intros Hpusha Hpopb Hwir [_ [_ Hnwir]].
    done.
  Qed.

  (* insert_pr_relaxed_stack.thy:293-294 *)
  Lemma wriI a b : is_push val a → is_pop val b → ¬ wir a b → wri b a.
  Proof.
    intros Hpusha Hpopb Hnwir. unfold wri. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:296-297 *)
  Lemma wriD a b : wri a b → is_pop val a ∧ is_push val b ∧ ¬ wir b a.
  Proof.
    intros [Hpopa [Hpushb Hnwir]]. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:299-300 *)
  Lemma wrrD a b : wrr a b → is_pop val a ∧ is_pop val b ∧ pre a b.
  Proof.
    intros [Hpopa [Hpopb Hpre]]. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:302-304 *)
  Lemma wiiD a b : wii a b → is_push val a ∧ is_push val b ∧ pre a b.
  Proof.
    intros [Hpusha [Hpushb Hpre]]. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:306-308 *)
  Lemma lem_wri ia ra ix rx rb :
    wri rb ia → val ia ra → val ix rx →
    ¬ (pre ia rb ∨ (pre ix rb ∧ pre rx ra ∧ wir ia rx)).
  Proof.
    intros Hwri Hvalia Hvalix.
    destruct (wriD _ _ Hwri) as [Hpoprb [Hpushia Hnwir]].
    intros [Hpreiarb | [Hpreixrb [Hprerxra Hwiriarx]]].
    - (* Case: pre ia rb *)
      apply Hnwir. apply wir_intro; done.
    - (* Case: pre ix rb ∧ pre rx ra ∧ wir ia rx *)
      apply Hnwir.
      destruct (lem_val_then_push_and_pop _ _ Hvalix) as [Hpushix Hpoprx].
      destruct (lem_val_then_push_and_pop _ _ Hvalia) as [_ Hpopra].
      (* push_pop_ordered gives ir ix ra or ir ra ix *)
      destruct (push_pop_ordered ix ra Hpushix Hpopra) as [Hirixra | Hirraix].
      + (* ir ix ra: use wir_right_rec *)
        (* wir_right_rec ix rx ia ra rb needs: val ix rx, val ia ra, is_pop rb,
           pre ix rb, pre rx ra, wir ia rx. All available. *)
        eapply (wir_right_rec ix rx ia ra rb); done.
      + (* ir ra ix: derive contradiction via acyclicity *)
        exfalso.
        (* val ix rx gives pre ix rx *)
        pose proof (val_then_pr _ _ Hvalix) as Hpreixrx.
        (* Cycle: ra -> ix (ir), ix -> rx (pre), rx -> ra (pre) *)
        apply (pr_u_ir_acyclic ra).
        eapply tc_l; first (right; exact Hirraix).
        eapply tc_l; first (left; exact Hpreixrx).
        apply tc_once. left. exact Hprerxra.
  Qed.

  (* insert_pr_relaxed_stack.thy:310-323 *)
  Lemma lem_rwir_then_ir a b : rwir a b → ir a b.
  Proof.
    intros Hrwir. induction Hrwir as [a' b' Hpre Hpush Hpop |
                                       a' b' ix rx ra Hvalix Hvala Hpopb Hprixb Hprrxra Hprbrx Hrwir IH].
    - (* rwir_intro: pre a b, is_push a, is_pop b *)
      apply lem_push_pr_pop_then_ir; done.
    - (* rwir_step *)
      destruct Hpopb as [ib Hib].
      destruct (lem_val_then_push_and_pop _ _ Hvalix) as [Hpushix Hpoprx].
      destruct (lem_val_then_push_and_pop _ _ Hvala) as [Hpusha Hpopra].
      destruct (lem_val_then_push_and_pop _ _ Hib) as [Hpushib Hpopb'].
      (* Need to show ir a' b'. We have ir a' rx from IH. *)
      (* Use push_pop_ordered: ir a' b' ∨ ir b' a' *)
      destruct (push_pop_ordered a' b' Hpusha Hpopb') as [Hirab | Hirba].
      + (* ir a' b' - done *)
        done.
      + (* ir b' a' - contradiction using insI and ipr_ooo *)
        exfalso.
        (* From insI ix a' b': ins ix a' *)
        assert (Hins : ins ix a').
        { apply (insI ix a' b'); done. }
        (* From ipr_ooo ix rx a' ra: pre ra rx *)
        pose proof (ipr_ooo _ _ _ _ Hvalix Hvala Hins IH) as Hprarx.
        (* But we have Hprrxra : pre rx ra *)
        (* By antisymmetry, ra = rx, which contradicts irreflexivity with pre rx ra *)
        assert (ra = rx) by (by eapply wf_pre_antisymmetric).
        subst rx.
        by eapply wf_pre_irreflexive.
  Qed.

  (* insert_pr_relaxed_stack.thy:325-326 *)
  Lemma lem_wir_then_ir a b : wir a b → ir a b.
  Proof.
    intros Hwir. apply lem_rwir_then_ir. apply lem_wir_then_rwir. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:328-338 *)
  Lemma lem_ir_then_wri a b : ir a b → is_pop val a → is_push val b → wri a b.
  Proof.
    intros Hirab Hpopa Hpushb.
    unfold wri. split; [done|split;[done|]].
    (* Need to show ¬ wir b a *)
    intros Hwirba.
    (* From wir b a, we get ir b a *)
    pose proof (lem_wir_then_ir _ _ Hwirba) as Hirba.
    (* Now we have ir a b and ir b a, which forms a cycle in pre ∪ ir *)
    apply (pr_u_ir_acyclic a).
    eapply tc_l; first (right; exact Hirab).
    apply tc_once. right. exact Hirba.
  Qed.

  (* insert_pr_relaxed_stack.thy:340-343 *)
  Lemma lem_wir_then_not_rev_pr a b : wir a b → ¬ pre b a.
  Proof.
    intros Hwir Hpreba.
    induction Hwir as [a' b' Hpre Hpush Hpop |
                        a' b' ix rx ra Hvalix Hvala [ib Hib] Hwir1 Hprrxra Hprbrx Hwir2 IH1 IH2].
    - (* wir_intro: pre a b, is_push a, is_pop b *)
      (* We have pre a' b' and pre b' a'. By antisymmetry a' = b'. *)
      (* But pre a' a' contradicts irreflexivity *)
      assert (a' = b') by (by eapply wf_pre_antisymmetric).
      subst. by eapply wf_pre_irreflexive.
    - (* wir_step *)
      destruct (lem_val_then_push_and_pop _ _ Hvalix) as [Hpushix Hpoprx].
      destruct (lem_val_then_push_and_pop _ _ Hvala) as [Hpusha Hpopra].
      destruct (lem_val_then_push_and_pop _ _ Hib) as [Hpushib Hpopb'].
      (* We have pre b' a' (from Hpreba). *)
      (* From pre b' a', is_pop b', is_push a', we get ir b' a' via lem_pop_pr_push_then_ir *)
      assert (Hirba : ir b' a') by (apply lem_pop_pr_push_then_ir; done).
      assert (Hwriba : wri b' a') by (apply lem_ir_then_wri; done).
      (* From wri b' a', we have ¬ wir a' b' *)
      destruct Hwriba as [_ [_ Hnwir]].
      (* But we can construct wir a' b' using wir_left_right_rec *)
      apply Hnwir.
      apply (wir_left_right_rec ix rx a' ra b'); done.
  Qed.

  (* insert_pr_relaxed_stack.thy:345-349 *)
  Lemma lem_pr_then_wri a b : pre a b → is_pop val a → is_push val b → wri a b.
  Proof.
    intros Hpre Hpopa Hpushb.
    apply wriI; try done.
    intros Hwirba.
    eapply lem_wir_then_not_rev_pr; eauto.
  Qed.

  (* insert_pr_relaxed_stack.thy:351-383 *)
  Lemma lem_pr_in_pr_witness : subrelation pre pr_witness.
  Proof.
    intros a b Hpre.
    (* Get push/pop status of a and b from def_push_or_pop *)
    destruct (def_push_or_pop _ _ Hpre) as [[c [Hvaca | Hvca]] [d [Hvadb | Hvdb]]].
    - (* a is push (val a c), b is push (val d b) *)
      destruct (lem_val_then_push_and_pop _ _ Hvaca) as [Hpusha _].
      destruct (lem_val_then_push_and_pop _ _ Hvadb) as [Hpushb _].
      (* wii a b *)
      unfold pr_witness. apply tc_once. left. right.
      unfold wii. done.
    - (* a is push (val a c), b is pop (val b d) *)
      destruct (lem_val_then_push_and_pop _ _ Hvaca) as [Hpusha _].
      destruct (lem_val_then_push_and_pop _ _ Hvdb) as [_ Hpopb].
      (* wir a b via wir_intro *)
      unfold pr_witness. apply tc_once. left. left. left.
      apply wir_intro; done.
    - (* a is pop (val c a), b is push (val d b) *)
      destruct (lem_val_then_push_and_pop _ _ Hvca) as [_ Hpopa].
      destruct (lem_val_then_push_and_pop _ _ Hvadb) as [Hpushb _].
      (* wri a b via lem_pr_then_wri *)
      unfold pr_witness. apply tc_once. left. left. right.
      apply lem_pr_then_wri; done.
    - (* a is pop (val c a), b is pop (val b d) *)
      destruct (lem_val_then_push_and_pop _ _ Hvca) as [_ Hpopa].
      destruct (lem_val_then_push_and_pop _ _ Hvdb) as [_ Hpopb].
      (* wrr a b *)
      unfold pr_witness. apply tc_once. right.
      unfold wrr. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:385-394 *)
  Lemma lem_wri_wir_then_pr ra ib rc : wri ra ib → wir ib rc → pre ra rc.
  Proof.
    intros Hwri Hwir.
    destruct (lem_wri_then_pop_and_push _ _ Hwri) as [Hpopra Hpushib].
    destruct (lem_wir_then_push_and_pop _ _ Hwir) as [Hpushib' Hpoprc].
    destruct (decide (ra = rc)) as [->|Hneq].
    - (* ra = rc - contradiction with lem_wir_then_not_wri *)
      exfalso.
      apply (lem_wir_then_not_wri ib rc Hpushib' Hpoprc Hwir).
      destruct Hwri as [_ [_ Hnwir]]. done.
    - (* ra ≠ rc - use pop_ordered *)
      destruct (ipr_pop_ordered ra rc Hpopra Hpoprc Hneq) as [Hpre | Hprerc].
      + (* pre ra rc - done *)
        done.
      + (* pre rc ra - extend wir on right, then contradiction *)
        exfalso.
        assert (Hwiribra : wir ib ra) by (apply (lem_wir_pr_then_wir _ rc); done).
        apply (lem_wir_then_not_wri ib ra Hpushib' Hpopra Hwiribra).
        destruct Hwri as [_ [_ Hnwir]]. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:396-404 *)
  Lemma lem_pr_wri_then_wri ra rb ic : wrr ra rb → wri rb ic → wri ra ic.
  Proof.
    intros Hwrr Hwri.
    destruct (wrrD _ _ Hwrr) as [Hpopra [Hpoprb Hprearb]].
    destruct (wriD _ _ Hwri) as [Hpoprb' [Hpushic Hnwir]].
    apply wriI; try done.
    intros Hwiricra.
    (* If wir ic ra, extend on right with pre ra rb to get wir ic rb *)
    assert (Hwiricrb : wir ic rb) by (apply (lem_wir_pr_then_wir _ ra); done).
    apply Hnwir. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:406-407 *)
  Lemma lem_ir_wir_then_pr a b c : rwir a b → ir c a → pre c b.
  Proof.
    intros Hrwir Hirca.
    (* From rwir a b, get is_push val a and is_pop val b *)
    destruct (lem_rwir_then_push_and_pop _ _ Hrwir) as [Hpusha Hpopb].
    (* From ir c a and is_push val a, get is_pop val c *)
    assert (Hpopc : is_pop val c) by (eapply ir_push_and_pop2; eauto).
    (* From ir c a, is_pop c, is_push a, we get wri c a *)
    assert (Hwrica : wri c a) by (apply lem_ir_then_wri; done).
    (* From rwir a b, we get wir a b *)
    assert (Hwirab : wir a b) by (apply lem_rwir_then_wir; done).
    (* From wri c a and wir a b, we get pre c b *)
    apply (lem_wri_wir_then_pr c a b); done.
  Qed.

  (* insert_pr_relaxed_stack.thy:409-419 *)
  Lemma lem_ooo_infer_ir ia ra ib rb : val ia ra → val ib rb → ins ia ib → pre ra rb → ir ra ib.
  Proof.
    intros Hvalia Hvalib Hins Hprerb.
    destruct (lem_val_then_push_and_pop _ _ Hvalia) as [Hpushia Hpopra].
    destruct (lem_val_then_push_and_pop _ _ Hvalib) as [Hpushib Hpoprb].
    (* Proof by contradiction: assume ¬ ir ra ib *)
    destruct (push_pop_ordered ib ra Hpushib Hpopra) as [Hiriba|Hir]; [|done].
    exfalso.
    (* From ipr_ooo: val ia ra, val ib rb, ins ia ib, ir ib ra → pre rb ra *)
    assert (Hprerba : pre rb ra) by (apply (ipr_ooo ia ra ib rb); done).
    (* But pre ra rb and pre rb ra means ra = rb by antisymmetry *)
    assert (ra = rb) by (by eapply wf_pre_antisymmetric).
    subst rb.
    (* pre ra ra contradicts irreflexivity *)
    by eapply wf_pre_irreflexive.
  Qed.

  (* insert_pr_relaxed_stack.thy:421-427 *)
  Lemma lem_wir_then_pop_pr a ra b : wir a b → val a ra → ¬ pre a b → pre b ra.
  Proof.
    intros Hwir Hvala Hnpre.
    destruct (wirD _ _ Hwir) as [Hpre | (ix & rx & ra' & Hvalix & Hvala' & Hpopb & Hwir1 & Hprrxra' & Hprbrx & Hwir2)].
    - (* pre a b - contradicts Hnpre *)
      contradiction.
    - (* step case *)
      (* ra' = ra by def_pop_once *)
      assert (ra' = ra) by (eapply def_pop_once; eauto). subst ra'.
      (* pre b rx and pre rx ra gives pre b ra by transitivity *)
      etrans; [exact Hprbrx | exact Hprrxra'].
  Qed.

  (* insert_pr_relaxed_stack.thy:429-461 *)
  Lemma lem_pr_wir_then_wir a b c : wir a b → is_push val c → pre c a → wir c b.
  Proof.
    intros Hwir [rc Hcrc] Hpreca.
    destruct (lem_wir_then_push_and_pop _ _ Hwir) as [Hpusha Hpopb].
    destruct Hpusha as [ra Hara].
    destruct (lem_val_then_push_and_pop _ _ Hcrc) as [Hpushc Hpoprc].
    destruct (lem_val_then_push_and_pop _ _ Hara) as [Hpusha Hpopra].
    destruct (decide (ra = rc)) as [->|Hneq].
    - (* ra = rc: then a = c by def_push_once *)
      assert (a = c) by (eapply def_push_once; eauto). subst c. done.
    - destruct (ipr_pop_ordered ra rc Hpopra Hpoprc Hneq) as [Hprarc|Hprcra].
      + (* pre ra rc *)
        destruct (decide (pre a b)) as [Hpreab|Hnotpreab].
        * (* pre a b: pre c b by transitivity, then wir_intro *)
          apply wir_intro.
          -- etrans; done.
          -- exists rc. done.
          -- done.
        * (* ¬ pre a b: use wir_step *)
          assert (Hprebra : pre b ra).
          { apply (lem_wir_then_pop_pr a ra b Hwir Hara Hnotpreab). }
          assert (Hwircra : wir c ra).
          { apply wir_intro; [|exists rc|]; done || (etrans; first done; apply val_then_pr; done). }
          apply (wir_step c b a ra rc Hara Hcrc Hpopb Hwir Hprarc Hprebra Hwircra).
      + (* pre rc ra *)
        (* This case uses ooo reasoning *)
        assert (Hinscra : ins c a) by (apply lem_pr_then_ins; [exists rc; done | exists ra; done | done]).
        (* Check if ir a rc or ir rc a *)
        destruct (push_pop_ordered a rc Hpusha Hpoprc) as [Hirarc|Hirca].
        * (* ir a rc *)
          (* Derive wri rc a *)
          assert (Hwrica : wri rc a).
          { apply wriI; [exists ra; done | done |].
            intros Hwirarc.
            pose proof (lem_wir_then_ir _ _ Hwirarc) as Hirarc'.
            pose proof (ipr_ooo c rc a ra Hcrc Hara Hinscra Hirarc') as Hprerarc.
            assert (ra = rc) by (by eapply wf_pre_antisymmetric).
            done. }
          assert (Hprercb : pre rc b) by (apply (lem_wri_wir_then_pr rc a); done).
          assert (Hwircrc : wir c rc).
          { apply wir_intro; [apply val_then_pr; done | exists rc; done | exists c; done]. }
          (* Extend wir c rc on the right by pre rc b using lem_wir_pr_then_wir *)
          (* lem_wir_pr_then_wir : wir a b → is_pop c → pre b c → wir a c *)
          apply (lem_wir_pr_then_wir c rc b Hwircrc Hpopb Hprercb).
        * (* ir rc a *)
          assert (Hwrica : wri rc a) by (apply lem_ir_then_wri; [done | done | exists ra; done]).
          assert (Hprercb : pre rc b) by (apply (lem_wri_wir_then_pr rc a); done).
          assert (Hwircrc : wir c rc).
          { apply wir_intro; [apply val_then_pr; done | exists rc; done | exists c; done]. }
          apply (lem_wir_pr_then_wir c rc b Hwircrc Hpopb Hprercb).
  Qed.

  (* insert_pr_relaxed_stack.thy:463-467 *)
  Lemma lem_wri_pr_then_wri ra ib ic : wri ra ib → wii ib ic → wri ra ic.
  Proof.
    intros Hwri Hwii.
    destruct (wriD _ _ Hwri) as [Hpopra [Hpushib Hnwir]].
    destruct (wiiD _ _ Hwii) as [Hpushib' [Hpushic Hpreibic]].
    apply wriI; try done.
    intros Hwicra.
    (* If wir ic ra holds, then by lem_pr_wir_then_wir with pre ib ic, we get wir ib ra *)
    assert (Hwibra : wir ib ra) by (apply (lem_pr_wir_then_wir ic ra); done).
    done.
  Qed.

  (* insert_pr_relaxed_stack.thy:469-470 *)
  Lemma lem_wir_wri_then_not_pr ia rb ic : wir ia rb → wri rb ic → ¬ pre ic ia.
  Proof.
    intros Hwir Hwri Hpreicia.
    destruct (wriD _ _ Hwri) as [Hpoprb [Hpushic Hnwir]].
    (* If pre ic ia holds, and is_push ic, and wir ia rb, then by lem_pr_wir_then_wir we get wir ic rb *)
    assert (Hwicrb : wir ic rb) by (apply (lem_pr_wir_then_wir ia rb); done).
    done.
  Qed.

  (* insert_pr_relaxed_stack.thy:472-490 *)
  Lemma pr_witnessD a b :
    pr_witness a b →
    pre a b ∨
    (is_push val a ∧ is_push val b ∧ (∃ c, wir a c ∧ wri c b)) ∨
    (is_push val a ∧ is_pop val b ∧ wir a b) ∨
    (is_pop val a ∧ is_push val b ∧ wri a b).
  Proof.
    unfold pr_witness.
    (* Use induction on transitive closure *)
    intros Htc. induction Htc as [x y Hstep | x y z Hstep Htcyz IHyz].
    - (* Base case: single step *)
      destruct Hstep as [[[Hwir|Hwri]|Hwii]|Hwrr].
      + (* wir *)
        right. right. left.
        destruct (lem_wir_then_push_and_pop _ _ Hwir) as [Hpush Hpop].
        done.
      + (* wri *)
        right. right. right.
        destruct (lem_wri_then_pop_and_push _ _ Hwri) as [Hpop Hpush].
        done.
      + (* wii *)
        destruct (wiiD _ _ Hwii) as [Hpusha [Hpushb Hpre]].
        left. done.
      + (* wrr *)
        destruct (wrrD _ _ Hwrr) as [Hpopa [Hpopb Hpre]].
        left. done.
    - (* Inductive case: Hstep is R x y, Htcyz is tc R y z, IHyz is IH for y z *)
      destruct Hstep as [[[Hwir|Hwri]|Hwii]|Hwrr].
      + (* wir x y: is_push x, is_pop y *)
        destruct (lem_wir_then_push_and_pop _ _ Hwir) as [Hpushx Hpopy].
        destruct IHyz as [Hpreyz | [[Hpushy [Hpushz [c [Hwircz Hwricz]]]] |
                          [[Hpushy [Hpopz Hwiryz]] | [Hpopy' [Hpushz Hwriyz]]]]].
        * (* pre y z *)
          destruct (def_push_or_pop _ _ Hpreyz) as [_ [d [Hvald|Hvald]]].
          -- (* z is push *)
             right. left.
             destruct (lem_val_then_push_and_pop _ _ Hvald) as [Hpushz _].
             split; [done|split;[done|]].
             exists y. split; [done|].
             apply lem_pr_then_wri; done.
          -- (* z is pop *)
             right. right. left.
             assert (Hpopz : is_pop val z) by (exists d; done).
             split; [done|split;[done|]].
             apply (lem_wir_pr_then_wir x y z); done.
        * (* is_push y - contradiction with is_pop y *)
          exfalso.
          destruct Hpushy as [ry Hyry].
          destruct Hpopy as [iy Hiyy].
          eapply def_val_order; first exact Hyry. exists iy. left. done.
        * (* is_push y - contradiction with is_pop y *)
          exfalso.
          destruct Hpushy as [ry Hyry].
          destruct Hpopy as [iy Hiyy].
          eapply def_val_order; first exact Hyry. exists iy. left. done.
        * (* is_pop y, is_push z, wri y z - use wir-wri pair *)
          right. left.
          split; [done|split;[done|]].
          exists y. split; done.
      + (* wri x y: is_pop x, is_push y *)
        destruct (lem_wri_then_pop_and_push _ _ Hwri) as [Hpopx Hpushy].
        destruct IHyz as [Hpreyz | [[Hpushy' [Hpushz [c [Hwircz Hwricz]]]] |
                          [[Hpushy' [Hpopz Hwiryz]] | [Hpopy [Hpushz Hwriyz]]]]].
        * (* pre y z *)
          destruct (def_push_or_pop _ _ Hpreyz) as [[d [Hvald|Hvald]] _].
          -- (* y is push - consistent *)
             destruct (def_push_or_pop _ _ Hpreyz) as [_ [e [Hvale|Hvale]]].
             ++ (* z is push *)
                right. right. right.
                destruct (lem_val_then_push_and_pop _ _ Hvale) as [Hpushz _].
                split; [done|split;[done|]].
                assert (Hwiiye : wii y z) by (unfold wii; done).
                apply (lem_wri_pr_then_wri x y z); done.
             ++ (* z is pop *)
                left.
                assert (Hpopz : is_pop val z) by (exists e; done).
                (* y is push, z is pop, pre y z. So wir y z. *)
                assert (Hwiryz : wir y z).
                { apply wir_intro; done. }
                (* From wri x y and wir y z, use lem_wri_wir_then_pr to get pre x z *)
                apply (lem_wri_wir_then_pr x y z); done.
          -- (* y is pop - contradiction with is_push y *)
             exfalso.
             destruct Hpushy as [ry Hyry].
             eapply def_val_order; first exact Hyry.
             exists d. left. done.
        * (* wir y c, wri c z: extend wri on left *)
          right. right. right.
          destruct (lem_wir_then_push_and_pop _ _ Hwircz) as [Hpushy'' Hpopc].
          split; [done|split;[done|]].
          (* From wri x y and wir y c, get pre x c *)
          assert (Hprexc : pre x c) by (apply (lem_wri_wir_then_pr x y c); done).
          (* From pre x c where x and c are both pop, get wrr x c *)
          assert (Hwrrxc : wrr x c) by (unfold wrr; done).
          (* From wrr x c and wri c z, get wri x z *)
          apply (lem_pr_wri_then_wri x c z); done.
        * (* wir y z: y is push, z is pop *)
          left.
          (* From wri x y and wir y z, get pre x z *)
          apply (lem_wri_wir_then_pr x y z); done.
        * (* y is pop - contradiction with is_push y *)
          exfalso.
          destruct Hpushy as [ry Hyry].
          destruct Hpopy as [iy Hiyy].
          eapply def_val_order; first exact Hyry. exists iy. left. done.
      + (* wii x y: is_push x, is_push y, pre x y *)
        destruct (wiiD _ _ Hwii) as [Hpushx [Hpushy Hprexy]].
        destruct IHyz as [Hpreyz | [[Hpushy' [Hpushz [c [Hwircz Hwricz]]]] |
                          [[Hpushy' [Hpopz Hwiryz]] | [Hpopy [Hpushz Hwriyz]]]]].
        * (* pre y z: pre x z by transitivity *)
          left. etrans; done.
        * (* wir y c, wri c z: extend on left *)
          right. left.
          split; [done|split;[done|]].
          exists c. split.
          -- apply (lem_pr_wir_then_wir y c); done.
          -- done.
        * (* wir y z: extend on left *)
          right. right. left.
          split; [done|split;[done|]].
          apply (lem_pr_wir_then_wir y z); done.
        * (* y is pop - contradiction with is_push y *)
          exfalso.
          destruct Hpushy as [ry Hyry].
          destruct Hpopy as [iy Hiyy].
          eapply def_val_order; first exact Hyry. exists iy. left. done.
      + (* wrr x y: is_pop x, is_pop y, pre x y *)
        destruct (wrrD _ _ Hwrr) as [Hpopx [Hpopy Hprexy]].
        destruct IHyz as [Hpreyz | [[Hpushy [Hpushz [c [Hwircz Hwricz]]]] |
                          [[Hpushy [Hpopz Hwiryz]] | [Hpopy' [Hpushz Hwriyz]]]]].
        * (* pre y z: pre x z by transitivity *)
          left. etrans; done.
        * (* y is push - contradiction with is_pop y *)
          exfalso.
          destruct Hpushy as [ry Hyry].
          destruct Hpopy as [iy Hiyy].
          eapply def_val_order; first exact Hyry. exists iy. left. done.
        * (* y is push - contradiction with is_pop y *)
          exfalso.
          destruct Hpushy as [ry Hyry].
          destruct Hpopy as [iy Hiyy].
          eapply def_val_order; first exact Hyry. exists iy. left. done.
        * (* wri y z: extend on left *)
          right. right. right.
          split; [done|split;[done|]].
          apply (lem_pr_wri_then_wri x y); done.
  Qed.

  (* insert_pr_relaxed_stack.thy:492-493 *)
  Lemma pr_witnessI1 a b : pre a b → pr_witness a b.
  Proof.
    intros Hpre.
    apply lem_pr_in_pr_witness. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:495-503 *)
  Lemma pr_witnessI2 a b c : wir a c → wri c b → pr_witness a b.
  Proof.
    intros Hwir Hwri.
    unfold pr_witness.
    eapply tc_l; first (left; left; left; exact Hwir).
    apply tc_once. left. left. right. exact Hwri.
  Qed.

  (* insert_pr_relaxed_stack.thy:505-509 *)
  Lemma pr_witnessI3 a b : wir a b → pr_witness a b.
  Proof.
    intros Hwir.
    unfold pr_witness.
    apply tc_once. left. left. left. exact Hwir.
  Qed.

  (* insert_pr_relaxed_stack.thy:511-515 *)
  Lemma pr_witnessI4 a b : wri a b → pr_witness a b.
  Proof.
    intros Hwri.
    unfold pr_witness.
    apply tc_once. left. left. right. exact Hwri.
  Qed.

  (* insert_pr_relaxed_stack.thy:517-524 *)
  Lemma lem_pr_witness_irreflexive : Irreflexive pr_witness.
  Proof.
    intros a Haa.
    apply pr_witnessD in Haa.
    destruct Haa as [Hpre | [[Hpusha [Hpusha' [c [Hwir Hwri]]]] |
                      [[Hpusha [Hpopa _]] | [Hpopa [Hpusha _]]]]].
    - (* pre a a - contradicts irreflexivity *)
      by eapply wf_pre_irreflexive.
    - (* is_push a, wir a c, wri c a *)
      (* wri c a means ¬ wir a c, but we have wir a c *)
      destruct (wriD _ _ Hwri) as [_ [_ Hnwir]].
      done.
    - (* a is both push and pop - impossible *)
      destruct Hpusha as [ra Hara].
      destruct Hpopa as [ia Hiaa].
      eapply def_val_order; first exact Hara.
      exists ia. left. done.
    - (* a is both pop and push - impossible *)
      destruct Hpusha as [ra Hara].
      destruct Hpopa as [ia Hiaa].
      eapply def_val_order; first exact Hara.
      exists ia. left. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:526-527 *)
  Lemma lem_pr_witness_antisymmetric : Antisymmetric operation (=) pr_witness.
  Proof.
    intros a b Hab Hba.
    (* From pr_witness a b and pr_witness b a, we get pr_witness a a by transitivity *)
    assert (Haa : pr_witness a a).
    { unfold pr_witness in *. by eapply tc_transitive. }
    exfalso. eapply lem_pr_witness_irreflexive. exact Haa.
  Qed.

  (* Helper: pr_witness is transitive *)
  Local Lemma lem_pr_witness_transitive : Transitive pr_witness.
  Proof.
    intros a b c Hab Hbc.
    unfold pr_witness in *.
    eapply tc_transitive; eauto.
  Qed.


  (* insert_pr_relaxed_stack.thy:542-543 *)
  Lemma lem_pr_witness_pop_ordered a b :
    is_pop val a → is_pop val b → a ≠ b → pr_witness a b ∨ pr_witness b a.
  Proof.
    intros Hpopa Hpopb Hneq.
    destruct (ipr_pop_ordered a b Hpopa Hpopb Hneq) as [Hpre | Hpre].
    - left. apply lem_pr_in_pr_witness. done.
    - right. apply lem_pr_in_pr_witness. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:545-555 *)
  Lemma lem_pr_witness_push_pop_ordered a b :
    is_push val a → is_pop val b → pr_witness a b ∨ pr_witness b a.
  Proof.
    intros Hpusha Hpopb.
    destruct (lem_wir_wri_total a b Hpusha Hpopb) as [Hwir | Hwri].
    - left. apply pr_witnessI3. done.
    - right. apply pr_witnessI4. done.
  Qed.


  (* Helper: pr_witness preserves push_or_pop *)
  Local Lemma lem_pr_witness_push_or_pop a b :
    pr_witness a b → (∃ c, val a c ∨ val c a) ∧ (∃ c, val b c ∨ val c b).
  Proof.
    intros Hw.
    destruct (pr_witnessD _ _ Hw) as [Hpre|[[Hpusha [Hpushb _]]|[[Hpusha [Hpopb _]]|[Hpopa [Hpushb _]]]]].
    - exact (def_push_or_pop _ _ Hpre).
    - destruct Hpusha as [ra Hara]. destruct Hpushb as [rb Hbrb].
      split; [exists ra; left|exists rb; left]; done.
    - destruct Hpusha as [ra Hara]. destruct Hpopb as [ib Hibb].
      split; [exists ra; left|exists ib; right]; done.
    - destruct Hpopa as [ia Hiaa]. destruct Hpushb as [rb Hbrb].
      split; [exists ia; right|exists rb; left]; done.
  Qed.

  (* Helper: val implies not pr_witness (reverse direction) *)
  Local Lemma lem_val_then_not_pr_witness a b : val a b → ¬ pr_witness b a.
  Proof.
    intros Hval Hpr.
    (* val a b means a is push, b is pop *)
    destruct (lem_val_then_push_and_pop _ _ Hval) as [Hpusha Hpopb].
    (* pr_witness b a with b pop and a push *)
    apply pr_witnessD in Hpr.
    destruct Hpr as [Hpre|[[Hpushb _]|[[Hpushb _]|[Hpopb' [Hpusha' Hwri]]]]].
    - (* pre b a - contradicts val_then_not_pr *)
      eapply def_val_then_not_pr. exact Hval. done.
    - (* b is push - contradiction with b is pop *)
      destruct Hpushb as [rb Hbrb]. destruct Hpopb as [ib Hibb].
      eapply def_val_order; first exact Hbrb. exists ib. left. done.
    - (* b is push - contradiction with b is pop *)
      destruct Hpushb as [rb Hbrb]. destruct Hpopb as [ib Hibb].
      eapply def_val_order; first exact Hbrb. exists ib. left. done.
    - (* wri b a: b is pop, a is push, ¬ wir a b *)
      (* But val a b gives wir a b via wir_intro *)
      destruct (wriD _ _ Hwri) as [_ [_ Hnwir]].
      apply Hnwir.
      apply wir_intro.
      + apply val_then_pr. done.
      + exact Hpusha.
      + exact Hpopb.
  Qed.

  (* insert_pr_relaxed_stack.thy:529-540 *)
  Lemma lem_pr_witness_wellformed : WellformedHistory pr_witness val.
  Proof.
    constructor.
    - (* Transitive pr_witness *)
      exact lem_pr_witness_transitive.
    - (* Antisymmetric pr_witness *)
      exact lem_pr_witness_antisymmetric.
    - (* Irreflexive pr_witness *)
      exact lem_pr_witness_irreflexive.
    - (* FinitePredicate - same val, so same finite ops *)
      exact operation_finite.
    - exact def_push_once.
    - exact def_pop_once.
    - exact def_val_order.
    - exact lem_pr_witness_push_or_pop.
    - exact lem_val_then_not_pr_witness.
  Qed.


  (* insert_pr_relaxed_stack.thy:557-573 *)
  Lemma lem_pr_wri_ooo ia ra ib rb rc :
    pre ia rc → wri rc ib → val ia ra → val ib rb → wir ib ra → pre rb ra.
  Proof.
    intros Hpreiarc Hwrirc Hvalia Hvalib Hwiribra.
    destruct (lem_val_then_push_and_pop _ _ Hvalia) as [Hpushia Hpopra].
    destruct (lem_val_then_push_and_pop _ _ Hvalib) as [Hpushib Hpoprb].
    destruct (wriD _ _ Hwrirc) as [Hpoprc [Hpushib' Hnwiribrc]].
    destruct (decide (ra = rb)) as [Heq|Hneq].
    - (* ra = rb *)
      exfalso.
      subst rb.
      (* val ia ra and val ib ra, so ia = ib by def_push_once *)
      assert (ia = ib) by (eapply def_push_once; eauto).
      subst ib.
      (* wir ia ra holds from val_then_pr and wir_intro *)
      assert (Hwiriara : wir ia ra) by (apply wir_intro; [apply val_then_pr; done | done | done]).
      (* But wri rc ia requires ¬wir ia rc. Is ia = rc possible? *)
      (* From pre ia rc (ia push, rc pop), wir ia rc if pre ia rc, is_push ia, is_pop rc *)
      assert (Hwiriarc : wir ia rc) by (apply wir_intro; done).
      apply Hnwiribrc. done.
    - (* ra ≠ rb *)
      destruct (ipr_pop_ordered ra rb Hpopra Hpoprb Hneq) as [Hprarb|Hprrba].
      + (* pre ra rb *)
        exfalso.
        (* From wir ib ra, pre ra rb, get wir ib rb by lem_wir_pr_then_wir *)
        assert (Hwiribrb : wir ib rb) by (apply (lem_wir_pr_then_wir ib ra rb); done).
        (* Need to derive wir ib rc to contradict Hnwiribrc *)
        (* From pre ia rc (ia push, rc pop), derive wir ia rc *)
        assert (Hwiriarc : wir ia rc) by (apply wir_intro; done).
        apply Hnwiribrc.
        apply (wir_left_right_rec ia ra ib rb rc); done.
      + (* pre rb ra *)
        done.
  Qed.

  (* insert_pr_relaxed_stack.thy:575-581 *)
  Lemma lem_wir_wri_ooo ia ra ib rb rc :
    wir ia rc → wri rc ib → val ia ra → val ib rb → wir ib ra → pre rb ra.
  Proof.
    intros Hwiriarc Hwrirc Hvalia Hvalib Hwiribra.
    destruct (lem_val_then_push_and_pop _ _ Hvalia) as [Hpushia Hpopra].
    destruct (lem_val_then_push_and_pop _ _ Hvalib) as [Hpushib Hpoprb].
    destruct (decide (ra = rb)) as [Heq|Hneq].
    - (* ra = rb *)
      exfalso.
      subst rb.
      destruct (wriD _ _ Hwrirc) as [Hpoprc [Hpushib' Hnwiribrc]].
      (* From wir ia rc, get ir ia rc *)
      assert (Hiriarc : ir ia rc) by (apply lem_wir_then_ir; done).
      (* rc is pop (from ir ia rc where ia is push) *)
      assert (Hpoprc' : is_pop val rc) by (eapply ir_push_and_pop1; eauto).
      (* val ia ra and val ib ra, so ia = ib by def_push_once *)
      assert (ia = ib) by (eapply def_push_once; eauto).
      subst ib.
      apply Hnwiribrc. done.
    - (* ra ≠ rb *)
      destruct (ipr_pop_ordered ra rb Hpopra Hpoprb Hneq) as [Hprarb|Hprrba].
      + (* pre ra rb *)
        exfalso.
        (* From wir ib ra, pre ra rb, get wir ib rb by lem_wir_pr_then_wir *)
        assert (Hwiribrb : wir ib rb) by (apply (lem_wir_pr_then_wir ib ra rb); done).
        (* From wir ia rc, ir ia rc *)
        assert (Hiriarc : ir ia rc) by (apply lem_wir_then_ir; done).
        (* rc is pop (from ir ia rc where ia is push) *)
        assert (Hpoprc : is_pop val rc) by (eapply ir_push_and_pop1; eauto).
        destruct (wriD _ _ Hwrirc) as [_ [_ Hnwiribrc]].
        (* Need to derive wir ib rc to contradict Hnwiribrc *)
        apply Hnwiribrc.
        apply (wir_left_right_rec ia ra ib rb rc); done.
      + (* pre rb ra *)
        done.
  Qed.

  (* insert_pr_relaxed_stack.thy:583-602 *)
  Lemma lem_pr_witness_ooo ia ra ib rb :
    val ia ra → val ib rb → pr_witness ia ib → pr_witness ib ra → pr_witness rb ra.
  Proof.
    intros Hvalia Hvalib Hpwiaib Hpwibra.
    destruct (lem_val_then_push_and_pop _ _ Hvalia) as [Hpushia Hpopra].
    destruct (lem_val_then_push_and_pop _ _ Hvalib) as [Hpushib Hpoprb].
    (* Destruct pr_witness ia ib *)
    apply pr_witnessD in Hpwiaib.
    destruct Hpwiaib as [Hpreiaib | [[_ [_ [c [Hwiriac Hwricib]]]] | [[_ [Hpopib _]] | [Hpopia _]]]].
    - (* Case 1: pre ia ib *)
      (* Destruct pr_witness ib ra *)
      apply pr_witnessD in Hpwibra.
      destruct Hpwibra as [Hpreibra | [[_ [Hpushra _]] | [[_ [_ Hwiribra]] | [Hpopib _]]]].
      + (* Case 1.1: pre ia ib ∧ pre ib ra *)
        (* ins ia ib, ir ib ra, then ipr_ooo *)
        assert (Hins : ins ia ib) by (apply lem_pr_then_ins; done).
        assert (Hiribra : ir ib ra) by (apply lem_push_pr_pop_then_ir; done).
        assert (Hprerba : pre rb ra) by (apply (ipr_ooo ia ra ib rb); done).
        apply lem_pr_in_pr_witness. done.
      + (* Case 1.2: ra is push - contradiction with ra being pop *)
        exfalso. destruct Hpushra as [rra Hrara]. destruct Hpopra as [ira Hirara].
        eapply def_val_order; first exact Hrara. exists ira. left. done.
      + (* Case 1.3: pre ia ib ∧ wir ib ra *)
        assert (Hins : ins ia ib) by (apply lem_pr_then_ins; done).
        assert (Hiribra : ir ib ra) by (apply lem_wir_then_ir; done).
        assert (Hprerba : pre rb ra) by (apply (ipr_ooo ia ra ib rb); done).
        apply lem_pr_in_pr_witness. done.
      + (* Case 1.4: ib is pop - contradiction with ib being push *)
        exfalso. destruct Hpopib as [iib Hiiib]. destruct Hpushib as [rib Hribib].
        eapply def_val_order; first exact Hribib. exists iib. left. done.
    - (* Case 2: wir ia c ∧ wri c ib *)
      (* Destruct pr_witness ib ra *)
      apply pr_witnessD in Hpwibra.
      destruct Hpwibra as [Hpreibra | [[_ [Hpushra _]] | [[_ [_ Hwiribra]] | [Hpopib _]]]].
      + (* Case 2.1: (wir ia c ∧ wri c ib) ∧ pre ib ra *)
        (* Construct wir ib ra from pre ib ra *)
        assert (Hwiribra : wir ib ra) by (apply wir_intro; done).
        assert (Hprerba : pre rb ra) by (apply (lem_wir_wri_ooo ia ra ib rb c); done).
        apply lem_pr_in_pr_witness. done.
      + (* Case 2.2: ra is push - contradiction *)
        exfalso. destruct Hpushra as [rra Hrara]. destruct Hpopra as [ira Hirara].
        eapply def_val_order; first exact Hrara. exists ira. left. done.
      + (* Case 2.3: (wir ia c ∧ wri c ib) ∧ wir ib ra *)
        assert (Hprerba : pre rb ra) by (apply (lem_wir_wri_ooo ia ra ib rb c); done).
        apply lem_pr_in_pr_witness. done.
      + (* Case 2.4: ib is pop - contradiction *)
        exfalso. destruct Hpopib as [iib Hiiib]. destruct Hpushib as [rib Hribib].
        eapply def_val_order; first exact Hribib. exists iib. left. done.
    - (* Case 3: ia push, ib pop with wir - contradiction since ib is push *)
      exfalso. destruct Hpopib as [iib Hiiib]. destruct Hpushib as [rib Hribib].
      eapply def_val_order; first exact Hribib. exists iib. left. done.
    - (* Case 4: ia pop - contradiction since ia is push *)
      exfalso. destruct Hpopia as [iia Hiiia]. destruct Hpushia as [ria Hriaia].
      eapply def_val_order; first exact Hriaia. exists iia. left. done.
  Qed.

  (* insert_pr_relaxed_stack.thy:604-616 *)
  Local Instance pr_witness_dec : RelDecision pr_witness.
  Proof.
    apply tc_decision. intros a b.
    unfold relation_union, Relation_Operators.union, wri, wii, wrr, is_push, is_pop.
    apply _.
  Qed.

  Theorem insert_pr_relaxed_stack_linearizable :
    ∃ prt (_ : RelDecision prt), subrelation pre prt ∧ InsertRelaxedStack prt val.
  Proof.
    exists pr_witness, _.
    split.
    - (* subrelation pre pr_witness *)
      intros a b Hpre. apply lem_pr_in_pr_witness. done.
    - (* InsertRelaxedStack pr_witness val *)
      constructor.
      + (* WellformedHistory pr_witness val *)
        exact lem_pr_witness_wellformed.
      + (* pop_ordered *)
        exact lem_pr_witness_pop_ordered.
      + (* push_pop_ordered *)
        exact lem_pr_witness_push_pop_ordered.
      + (* ir_ooo *)
        exact lem_pr_witness_ooo.
  Qed.

End insert_pr_relaxed_stack.
