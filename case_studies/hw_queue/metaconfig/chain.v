(* chain.v — Chain the per-operation specs into [hwq_library_il], then
   expose the end-to-end logically-atomic specs for users. *)

From stdpp Require Import base gmap propset.
From iris_logatom.pure_logic Require Import linear.
From iris_logatom.pure_logic.models Require Import bag_like.
From iris_logatom.pure_logic.metaconfig Require Import tracking.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris.heap_lang Require Import notation proofmode adequacy unwrap.
From iris_logatom.program_logic Require Import atomic_complete.
From iris_logatom.heap_lang Require Import mgc fork_free.

From case_studies.hw_queue Require Import impl.
From case_studies.hw_queue.metaconfig Require Import defs init enq deq.

Lemma call_ret_wrapper_spec `{!heapGS Σ, !traceG Σ, !hwqMcG Σ} :
  call_ret_wrapper_spec_type
    hwq_repr NotStuck
    (@valid_request hwq_model) op.
Proof.
  intros γ tracer q req Hreq.
  destruct Hreq as [(v_push & Hunboxed & ->) | ->].
  - exact (push_wrapper_spec γ tracer q v_push Hunboxed).
  - exact (pop_wrapper_spec γ tracer q).
Qed.

(* ====================================================================== *)
(* Library-level linearizability. *)

Lemma hwq_library_il sz :
  (0 < sz)%Z →
  library_initializable_linearizable (M := hwq_model) (init_hwq sz) op.
Proof.
  set (Σ := #[heapΣ; traceΣ; hwqMcΣ]).
  intros Hsz. split.
  - (* Init terminates and does not get stuck. *)
    intros σ.
    apply (heap_adequacy Σ) => ?. iIntros "_".
    rewrite /init_hwq.
    wp_pures. wp_lam.
    wp_apply (wp_allocN with "[//]") as (l) "_"; first done.
    wp_pures.
    wp_alloc l' as "_".
    wp_pures. done.
  - (* Linearizability of [op]. *)
    intros obj σ₀ t σ config' ts Hsteps Hadv_steps.
    opose proof (bdgjst_free (Σ:=Σ) hwq_repr _ _ op σ₀ obj t σ config' ts
                   _ _ I_lang_hwq_init Hsteps Hadv_steps)
      as (Hnot_stuck & Hilang).
    + intros ?. by apply init_spec.
    + intros ?. by apply call_ret_wrapper_spec.
    + split; first exact Hnot_stuck.
      destruct Hilang as [HIM Hpw].
      apply (proj1 (metaconfig_tracking_iff_linearizable ts)).
      split; assumption.
Qed.

(* ====================================================================== *)
(* End-to-end logically-atomic specs. *)

Section client_specs.
  Context `{!heapGS Σ}.
  Context `{!linearizabilityG (M := hwq_model) Σ}.

  Definition is_hwq_atomic γ q := is_P (M := hwq_model) op γ q.
  Definition hwq_content γ (ls : list val) := P_state (M := hwq_model) γ ls.

  Definition enqueue_wrapper : val := λ: "q" "v", wrap_op op "q" (SOME "v").
  Definition dequeue_wrapper : val := λ: "q", unwrap (wrap_op op "q" NONEV).

  Lemma new_queue_spec sz :
    (0 < sz)%Z →
    {{{ True }}}
      wrap_init (init_hwq sz) #()
    {{{ γ q, RET q; is_hwq_atomic γ q ∗ hwq_content γ [] }}}.
  Proof.
    intros Hsz.
    assert (Hseq : ∀ σ, sequential (init_hwq sz #()) σ).
    { intros ?. apply fork_free_sequential. compute_done. }
    pose proof (init_spec_full := logatom_complete_init _ _ Hseq
                  (hwq_library_il sz Hsz)).
    simpl in init_spec_full.
    apply init_spec_full.
  Qed.

  Lemma enqueue_spec γ (q v : val) :
    val_is_unboxed (SOMEV v) →
    is_hwq_atomic γ q ⊢
    <<{ ∀∀ ls, hwq_content γ ls }>>
      enqueue_wrapper q v @ ↑Nlogatom
    <<{ hwq_content γ (ls ++ [v]) | RET #() }>>.
  Proof.
    iIntros (Hunboxed) "#His_hwq %Φ AU".
    wp_lam. wp_pures.
    opose proof (logatom_complete_op _ _ (hwq_library_il 1 _) γ q (SOMEV v) _)
      as op_full_spec; first lia.
    { rewrite /valid_request. left. exists v. done. }
    awp_apply (op_full_spec with "His_hwq").
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (s) "Hcontent".
    iAaccIntro with "Hcontent"; first by iIntros "$ !>"; auto.
    iIntros (ls' y) "[Hcontent %Hrr] !>".
    destruct Hrr as (r & Henc & Hrr).
    change (SOMEV v) with (encode_request (Push v)) in Henc.
    apply (inj encode_request) in Henc. subst r.
    destruct Hrr as [-> ->].
    iFrame "Hcontent". auto.
  Qed.

  Lemma dequeue_spec γ (q : val) :
    is_hwq_atomic γ q ⊢
    <<{ ∀∀ ls, hwq_content γ ls }>>
      dequeue_wrapper q @ ↑Nlogatom
    <<{ ∃∃ l ls', ⌜ls = l :: ls'⌝ ∗ hwq_content γ ls' | RET l }>>.
  Proof.
    iIntros "#His_hwq %Φ AU".
    wp_lam.
    opose proof (logatom_complete_op _ _ (hwq_library_il 1 _) γ q NONEV _)
      as op_full_spec; first lia.
    { rewrite /valid_request. right. done. }
    awp_apply (op_full_spec with "His_hwq").
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (ls) "Hcontent".
    iAaccIntro with "Hcontent"; first by iIntros "$ !>"; auto.
    iIntros (ls' y) "[Hcontent %Hrr] !>".
    destruct Hrr as (r & Henc & Hrr).
    change (NONEV) with (encode_request Pop) in Henc.
    apply (inj encode_request) in Henc. subst r.
    destruct ls as [|l ls].
    { destruct Hrr. }
    destruct Hrr as [-> ->].
    iExists l, ls.
    iFrame "Hcontent". iSplit; first done.
    iIntros "HΦ !>".
    simpl.
    by wp_apply unwrap_spec.
  Qed.

End client_specs.
