(* The TS stack (Dodds, Haas, and Kirsch, POPL'15) is linearizable without prophecy variables:
   every trace of the most general client satisfies the premise of the vis/rr stack theorem
   (pure_logic/aspect/stack/vis.v), with the point of a push at its SP-pool insertion, the point
   of a pop at its start, and the commit of a pop at its successful taken-CAS. The invariant is
   an abstract state (pure.v) together with the physical state and the ghost resources (defs.v,
   resources.v, steps.v). The operations: timestamp.v, unlink.v, push.v; youngest.v, remove.v,
   check.v, tryrem.v, pop.v; init.v. *)

From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect Require Import bag stack.
From iris_logatom.pure_logic Require Import encodable linear.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import agree mono_list mono_nat.
From iris.base_logic Require Import invariants ghost_map ghost_var.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy lang notation tactics unwrap proofmode.
From iris.heap_lang.lib Require Import array.
From iris_logatom.heap_lang Require Import mgc fork_free.
From iris_logatom.heap_lang.lib Require Import thread_id.
From case_studies.ts_stack Require Import impl.
From case_studies.ts_stack.aspect Require Import pure defs push pop init.

Section proof.
  Context `{!heapGS Σ, !traceG Σ, !tsG Σ}.
  Implicit Types σ : tss.

  Lemma call_ret_wrapper_spec :
    call_ret_wrapper_spec_type repr_ts NotStuck (@valid_requests (stack_model MayEmpty (λ _, True))) ops.
  Proof.
    intros k γ tracer q req Hreq.
    destruct k as [|[|k]]; last by (simpl in Hreq; destruct Hreq).
    - rewrite /I_lang /mgc_inv /=. by apply push_wrapper_spec.
    - simpl in Hreq. subst req. rewrite /I_lang /mgc_inv /=. by apply pop_wrapper_spec.
  Qed.
End proof.

(* The TS stack is linearizable: every trace of the most general client satisfies the premise
   of the vis/rr stack theorem. *)
Lemma ts_stack_library_il (n : nat) :
  0 < n →
  library_initializable_linearizable (M:=stack_model MayEmpty (λ _, True)) (new_tsstack #n) ops.
Proof.
  set (Σ := #[heapΣ; traceΣ; tsΣ]).
  intros Hn. split.
  - intros σ.
    apply (heap_adequacy Σ) => ?. iIntros "_".
    iApply (init_spec n Hn with "[//]"). iIntros "!>" (γ obj) "_". done.
  - intros obj σ₀ t σ config' ts Hsteps Hadv_steps.
    opose proof (bdgjst_free (Σ:=Σ) repr_ts _ _ ops σ₀ obj t σ config' ts _ _ _ Hsteps Hadv_steps)
      as (Hconfig_not_stuck & Hwf & Hstack).
    + intros ?. by apply init_spec.
    + intros ?. by apply call_ret_wrapper_spec.
    + split; [apply per_tag_wellformed_bag_nil|apply I_stack_vis_nil].
    + split; first done.
      by apply stack_theorem_vis.
Qed.

Section spec.
  Context `{!heapGS Σ}.
  Context `{!linearizabilityG (M := stack_model MayEmpty (λ _, True)) Σ}.

  Let M := stack_model MayEmpty (λ _, True).

  Definition is_ts_stack γ q := is_P (M:=M) ops γ q.
  Definition ts_stack_content γ (ls : list val) := P_state (M := M) γ ls.

  Definition new_stack_wrapper : val := λ: "n", wrap_init (new_tsstack "n").
  Definition stack_push_wrapper : val := λ: "s" "v", wrap_op Push (ops!!!Push : val) "s" "v".
  Definition stack_pop_wrapper : val := λ: "s", wrap_op Pop (ops!!!Pop : val) "s" #().

  Lemma new_stack_spec (n : nat) :
    0 < n →
    {{{ True }}}
      new_stack_wrapper #n
    {{{ γ q, RET q; is_ts_stack γ q ∗ ts_stack_content γ [] }}}.
  Proof.
    intros Hn.
    assert (Hnv : to_val (new_tsstack #n) = None) by done.
    assert (Hseq : ∀ σ, sequential (new_tsstack #n) σ).
    { intros ?. apply fork_free_sequential. compute_done. }
    pose proof (init_spec := logatom_complete_init _ _ Hnv Hseq (ts_stack_library_il n Hn)).
    iIntros (Φ) "HT HΦ".
    wp_lam. iApply (init_spec with "HT HΦ").
  Qed.

  Lemma stack_push_spec γ (q v : val) :
    is_ts_stack γ q ⊢
    <<{ ∀∀ ls, ts_stack_content γ ls }>>
      stack_push_wrapper q v @ ↑Nlogatom
    <<{ ts_stack_content γ (v :: ls) | RET #() }>>.
  Proof.
    iIntros "#His %Φ AU".
    wp_lam. wp_pures.
    opose proof (logatom_complete_op _ _ Push (ts_stack_library_il 1 _) γ q v _) as op_spec; first lia.
    { done. }
    awp_apply (op_spec with "His").
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (s) "Hcontent".
    iAaccIntro with "Hcontent"; first by iIntros "$ !>"; auto.
    iIntros (ls' y) "[Hcontent %Hrr] !>".
    destruct Hrr as [-> ->].
    iFrame "Hcontent". auto.
  Qed.

  Lemma stack_pop_spec γ (q : val) :
    is_ts_stack γ q ⊢
    <<{ ∀∀ ls, ts_stack_content γ ls }>>
      stack_pop_wrapper q @ ↑Nlogatom
    <<{ ∃∃ ls' (r : val), ts_stack_content γ ls' ∗
          ⌜match ls with [] => ls' = [] ∧ r = NONEV | v :: l => ls' = l ∧ r = SOMEV v end⌝ | RET r }>>.
  Proof.
    iIntros "#His %Φ AU".
    wp_lam.
    opose proof (logatom_complete_op _ _ Pop (ts_stack_library_il 1 _) γ q #() _) as op_spec; first lia.
    { done. }
    awp_apply (op_spec with "His").
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (ls) "Hcontent".
    iAaccIntro with "Hcontent"; first by iIntros "$ !>"; auto.
    iIntros (ls' y) "[Hcontent %Hrr] !>".
    iExists ls', y. iFrame "Hcontent". iSplit; [|auto].
    iPureIntro. destruct ls; simpl in Hrr; naive_solver.
  Qed.
End spec.
