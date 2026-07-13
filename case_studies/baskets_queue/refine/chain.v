(* refine_chain.v: chain the plain specs proved in
  [refine_new_queue.v] and [refine_op_spec.v] via
  [bdgjst_free] into [bq_library_linearizable], and lift to a
  logically atomic spec via [program_logic/atomic_complete.v].  Mirrors
  [hw_queue/refine_chain.v]. *)

From iris.algebra Require Import auth excl gmap agree.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy primitive_laws notation proofmode.
From iris_logatom.heap_lang Require Import mgc fork_free.
From iris_logatom.heap_lang.lib Require Import trace.
From iris_logatom.pure_logic Require Import linear adequacy.
From iris_logatom.pure_logic.models Require Import bag_like.
From iris_logatom.pure_logic.refine Require Import absq absq_refines_absq0
                                                    absq0_linearizable
                                                    backward_simulation.

From case_studies.baskets_queue Require Import impl refine.defs
                                                refine.new_queue refine.op_spec.

Section bq_skeleton_chain.
  Local Notation Nbq := Nbq.
  Local Notation bq_inv_body := bq_inv_body.
  Local Notation is_bq := is_bq.
  Local Notation bq_repr := bq_repr.
  Local Notation init_bq := init_bq.
  Local Notation new_queue_spec := new_queue_spec.
  Local Notation op_spec := op_spec.

  Definition bq_valid_obj (obj : val) (σ : state) : Prop :=
    ∃ σ₀ efs, rtc erased_step ([init_bq #()], σ₀) (Val obj :: efs, σ).

  Theorem bq_library_linearizable :
    library_linearizable (M := queue_model MayEmpty bq_valid_value) op bq_valid_obj.
  Proof.
    set (Σ := #[heapΣ; traceΣ; bqΣ]).
    intros obj σ config' ts (σ₀ & efs & Hinit_steps) Hadv.
    pose proof (bdgjst_free (Σ:=Σ) bq_repr
                  (queue_model MayEmpty bq_valid_value).(valid_request)
                  init_bq op
                  σ₀ obj efs σ config' ts
                  new_queue_spec op_spec
                  I_lang_bq_init Hinit_steps Hadv)
      as [Hns HI_lang].
    split; [exact Hns|].
    (* [bdgjst_free]'s [I_lang_bq ts] conclusion is exactly
       [trace_refines_absq MayEmpty bq_valid_value ts]; the trace-level
       refine result then yields [trace_linearizable ts]. *)
    apply refines_absq_trace_linearizable. exact HI_lang.
  Qed.

  Lemma bq_library_initializable :
    library_initializable init_bq bq_valid_obj.
  Proof.
    set (Σ := #[heapΣ; traceΣ; bqΣ]).
    intros σ.
    eapply adequate_weaken.
    2: { apply (adequate_strengthen_reach _ _ _ (λ _ _, True)).
         apply (heap_adequacy Σ).
         iIntros (Hheap) "_".
         wp_apply (new_queue_spec _ with "[//]").
         iIntros (γ obj) "_". done.
    }
    intros v σ' [_ (efs & Hrtc)]. by exists σ, efs.
  Qed.

  Theorem bq_library_initializable_linearizable :
    library_initializable_linearizable (M := queue_model MayEmpty bq_valid_value) init_bq op.
  Proof.
    apply library_initializable_linearizable_iff.
    exists bq_valid_obj.
    split; [apply bq_library_initializable | apply bq_library_linearizable].
  Qed.
End bq_skeleton_chain.

(* ========================================================================= *)
(* Logically atomic spec for [wrap_op op x y]. *)

Section bq_logatom.
  Context `{!heapGS Σ}.
  Context `{!linearizabilityG (M := queue_model MayEmpty bq_valid_value) Σ}.

  Local Notation M := (queue_model MayEmpty bq_valid_value).

  Theorem bq_logatom_op_spec γ (x y : val) :
    M.(valid_request) y →
    is_P (M := M) op γ x ⊢
    <<{ ∀∀ s, P_state (M := M) γ s }>>
      wrap_op op x y @ ↑Nlogatom
    <<{ ∃∃ s' y', P_state (M := M) γ s' ∗
          ⌜M.(request_response) s y s' y'⌝ | RET y' }>>.
  Proof.
    apply (logatom_complete_op init_bq op).
    exact bq_library_initializable_linearizable.
  Qed.

  Corollary bq_logatom_init_spec :
    {{{ True }}}
      wrap_init init_bq #()
    {{{ γ r, RET r;
        is_P (M := M) op γ r ∗
        P_state (M := M) γ (s_init : M.(S)) }}}.
  Proof.
    apply (logatom_complete_init init_bq op).
    - intros ?. apply fork_free_sequential. compute_done.
    - exact bq_library_initializable_linearizable.
  Qed.
End bq_logatom.

(* ========================================================================= *)
(* End-to-end logically-atomic client specs, exposing the baskets queue as a
  data structure with enqueue/dequeue operations. Mirrors the
  [hw_queue/refine/chain.v] and [hw_queue/metaconfig/chain.v] client specs.
  Since the baskets queue is [MayEmpty], [dequeue] returns SOMEV v on a
  non-empty queue and NONEV on an empty queue, so the wrapper does not
  apply [unwrap]. *)

Section client_specs.
  Context `{!heapGS Σ}.
  Context `{!linearizabilityG (M := queue_model MayEmpty bq_valid_value) Σ}.

  Local Notation M := (queue_model MayEmpty bq_valid_value).

  Definition is_bq_atomic γ q := is_P (M := M) op γ q.
  Definition bq_content γ (ls : list val) := P_state (M := M) γ ls.

  Definition enqueue_wrapper : val := λ: "q" "v", wrap_op op "q" (SOME "v").
  Definition dequeue_wrapper : val := λ: "q", wrap_op op "q" NONEV.

  Lemma new_queue_spec :
    {{{ True }}}
      wrap_init init_bq #()
    {{{ γ q, RET q; is_bq_atomic γ q ∗ bq_content γ [] }}}.
  Proof.
    assert (Hseq : ∀ σ, sequential (init_bq #()) σ).
    { intros ?. apply fork_free_sequential. compute_done. }
    pose proof (init_spec_full :=
                  logatom_complete_init _ _ Hseq
                    bq_library_initializable_linearizable).
    simpl in init_spec_full.
    apply init_spec_full.
  Qed.

  Lemma enqueue_spec γ (q v : val) :
    val_is_unboxed (SOMEV v) →
    is_bq_atomic γ q ⊢
    <<{ ∀∀ ls, bq_content γ ls }>>
      enqueue_wrapper q v @ ↑Nlogatom
    <<{ bq_content γ (ls ++ [v]) | RET #() }>>.
  Proof.
    iIntros (Hunboxed) "#His_bq %Φ AU".
    wp_lam. wp_pures.
    opose proof (logatom_complete_op _ _
                  bq_library_initializable_linearizable
                  γ q (SOMEV v) _) as op_full_spec.
    { rewrite /valid_request. left. exists v. done. }
    awp_apply (op_full_spec with "His_bq").
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

  (* The [MayEmpty] dequeue's atomic post-state explicitly exposes both
     outcomes: empty queue (returns NONEV, state unchanged) and non-empty
     queue (returns SOMEV l, state advances to the tail). *)
  Lemma dequeue_spec γ (q : val) :
    is_bq_atomic γ q ⊢
    <<{ ∀∀ ls, bq_content γ ls }>>
      dequeue_wrapper q @ ↑Nlogatom
    <<{ ∃∃ ls' y,
          bq_content γ ls' ∗
          ⌜(ls = [] ∧ ls' = [] ∧ y = NONEV) ∨
           (∃ l, ls = l :: ls' ∧ y = SOMEV l)⌝ | RET y }>>.
  Proof.
    iIntros "#His_bq %Φ AU".
    wp_lam.
    opose proof (logatom_complete_op _ _
                  bq_library_initializable_linearizable
                  γ q NONEV _) as op_full_spec.
    { rewrite /valid_request. right. done. }
    awp_apply (op_full_spec with "His_bq").
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (ls) "Hcontent".
    iAaccIntro with "Hcontent"; first by iIntros "$ !>"; auto.
    iIntros (ls' y) "[Hcontent %Hrr] !>".
    destruct Hrr as (r & Henc & Hrr).
    change (NONEV) with (encode_request Pop) in Henc.
    apply (inj encode_request) in Henc. subst r.
    iExists ls', y. iFrame "Hcontent". iSplit; last by auto.
    iPureIntro. destruct ls as [|l ls_tail].
    - left. destruct Hrr as [-> ->]. done.
    - right. exists l. destruct Hrr as [-> ->]. done.
  Qed.

End client_specs.
