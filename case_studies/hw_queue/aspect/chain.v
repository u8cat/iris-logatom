(* This theory establishes the linearizability of Herlihy-Wing Queue using
a variant of Thomas Henzinger's queue theorem. The premise of the queue
theorem is verifed by Birkedal et al's Free Theorem. Then by our result,
we obtain a logatom triple of HWQ. The proof is split over the files of this
directory: defs.v (the invariant), init.v, push.v, and pop.v. *)
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect Require Import bag queue.
From iris_logatom.pure_logic Require Import encodable linear.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gset agree mono_list mono_nat.
From iris.base_logic Require Import invariants ghost_map.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy lang notation tactics unwrap.
From iris_logatom.heap_lang Require Import mgc fork_free.

From case_studies.hw_queue Require Import impl.
From case_studies.hw_queue.aspect Require Import defs init push pop.

Section proof.
  Context `{!heapGS Σ, !traceG Σ, !hwqG Σ}.

  Lemma call_ret_wrapper_spec : call_ret_wrapper_spec_type repr_queue NotStuck (@valid_requests (queue_model NeverEmpty (λ v, val_is_unboxed (SOMEV v)))) ops.
  Proof.
    intros n γ tracer q req Hreq.
    destruct n as [|[|n]]; last by (simpl in Hreq; destruct Hreq).
    - rewrite /I_lang /mgc_inv /=. by apply push_wrapper_spec.
    - simpl in Hreq. subst req.
      rewrite /I_lang /mgc_inv /=. by apply pop_wrapper_spec.
  Qed.
End proof.

Lemma hwq_library_il sz :
  (0 < sz)%Z →
  library_initializable_linearizable (M:=queue_model NeverEmpty (λ v, val_is_unboxed (SOMEV v))) (new_queue #sz) ops.
Proof.
  set (Σ := #[heapΣ; traceΣ; hwqΣ]).
  intros Hsz. split.
  - intros σ.
    apply (heap_adequacy Σ) => ?. iIntros "_".
    wp_lam.
    wp_apply (wp_allocN with "[//]") as (l) "_"; first done.
    wp_pures.
    wp_alloc l' as "_".
    wp_pures. done.
  - intros obj σ₀ t σ config' ts Hsteps Hadv_steps.
    opose proof (bdgjst_free (Σ:=Σ) repr_queue _ _ ops σ₀ obj t σ config' ts _ _ _ Hsteps Hadv_steps)
      as (Hconfig_not_stuck & Hwf & Hqueue).
    + intros ?. by apply init_spec.
    + intros ?. by apply call_ret_wrapper_spec.
    + split; [apply per_tag_wellformed_bag_nil | apply I_queue_nil].
    + split; first done.
      apply queue_theorem; assumption.
Qed.

Section spec.
  Context `{!heapGS Σ}.
  Context `{!linearizabilityG (M := queue_model NeverEmpty (λ v, val_is_unboxed (SOMEV v))) Σ}.

  Let M := (queue_model NeverEmpty (λ v, val_is_unboxed (SOMEV v))).

  Definition is_hwq γ q := is_P (M:=M) ops γ q.
  Definition hwq_content γ (ls : list val) := P_state (M := M) γ ls.

  Definition new_queue_wrapper: val := λ: "sz", wrap_init (new_queue "sz").
  Definition enqueue_wrapper: val := λ: "q" "v", wrap_op Push (ops!!!Push : val) "q" "v".
  Definition dequeue_wrapper: val := λ: "q", unwrap (wrap_op Pop (ops!!!Pop : val) "q" #()).

  Lemma new_queue_spec sz :
    (0 < sz)%Z →
    {{{ True }}}
      new_queue_wrapper #sz
    {{{ γ q, RET q; is_hwq γ q ∗ hwq_content γ [] }}}.
  Proof.
    intros Hsz.
    assert (Hnv : to_val (new_queue #sz) = None) by done.
    assert (Hseq : ∀ σ, sequential (new_queue #sz) σ).
    { intros ?. apply fork_free_sequential. compute_done. }
    pose proof (init_spec := logatom_complete_init _ _ Hnv Hseq
                  (hwq_library_il sz Hsz)).
    iIntros (Φ) "HT HΦ".
    wp_lam. iApply (init_spec with "HT HΦ").
  Qed.

  Lemma enqueue_spec γ (q v : val) :
    val_is_unboxed (SOMEV v) →
    is_hwq γ q ⊢
    <<{ ∀∀ ls, hwq_content γ ls }>>
      enqueue_wrapper q v @ ↑Nlogatom
    <<{ hwq_content γ (ls++[v]) | RET #() }>>.
  Proof.
    iIntros (Hunboxed) "#His_hwq %Φ AU".
    wp_lam. wp_pures.
    opose proof (logatom_complete_op _ _ Push (hwq_library_il 1 _) γ q v _)
      as op_spec; first lia.
    { exact Hunboxed. }
    awp_apply (op_spec with "His_hwq").
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (s) "Hcontent".
    iAaccIntro with "Hcontent"; first by iIntros "$ !>"; auto.
    iIntros (ls' y) "[Hcontent %Hrr] !>".
    destruct Hrr as [-> ->].
    iFrame "Hcontent". auto.
  Qed.

  Lemma dequeue_spec γ (q v : val) :
    is_hwq γ q ⊢
    <<{ ∀∀ ls, hwq_content γ ls }>>
      dequeue_wrapper q @ ↑Nlogatom
    <<{ ∃∃ l ls', ⌜ls = l :: ls'⌝ ∗ hwq_content γ ls' | RET l }>>.
  Proof.
    iIntros "#His_hwq %Φ AU".
    wp_lam.
    opose proof (logatom_complete_op _ _ Pop (hwq_library_il 1 _) γ q #() _)
      as op_spec; first lia.
    { done. }
    awp_apply (op_spec with "His_hwq").
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (ls) "Hcontent".
    iAaccIntro with "Hcontent"; first by iIntros "$ !>"; auto.
    iIntros (ls' y) "[Hcontent %Hrr] !>".
    destruct ls as [|l ls].
    { destruct Hrr. }
    destruct Hrr as [-> ->].
    iExists l, ls.
    iFrame "Hcontent". iSplit; first done.
    iIntros "HΦ !>".
    simpl.
    by wp_apply unwrap_spec.
  Qed.
End spec.
