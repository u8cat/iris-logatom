(* refine_chain.v: chain the plain specs proved in
  [refine_new_queue.v] and [refine_op_spec.v] via
  [bdgjst_free] into [hwq_library_linearizable], then lift to
  a logically atomic spec using [program_logic/atomic_complete.v]. *)

From iris.algebra Require Import auth excl gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy primitive_laws notation proofmode unwrap.
From iris_logatom.heap_lang Require Import mgc fork_free.
From iris_logatom.heap_lang.lib Require Import trace.
From iris_logatom.pure_logic Require Import linear adequacy.
From iris_logatom.pure_logic.models Require Import bag_like.
From iris_logatom.pure_logic.refine Require Import absq absq_refines_absq0
                                                    absq0_linearizable
                                                    backward_simulation.

From case_studies.hw_queue Require Import impl refine.defs
                                          refine.new_queue refine.op_spec.

Section hwq_skeleton_chain.
  Context (sz : Z).
  Hypothesis sz_pos : (0 < sz)%Z.

  Local Notation Nhwq := Nhwq.
  Local Notation hwq_inv_body := (hwq_inv_body sz).
  Local Notation is_hwq := (is_hwq sz).
  Local Notation hwq_repr := (hwq_repr sz).
  Local Notation init_hwq := (init_hwq sz).
  Local Notation new_queue_spec :=
    (new_queue_spec sz sz_pos).
  Local Notation op_spec :=
    (op_spec sz sz_pos).

  Definition hwq_valid_obj (obj : val) (σ : state) : Prop :=
    ∃ σ₀ efs, rtc erased_step ([init_hwq], σ₀) (Val obj :: efs, σ).

  Theorem hwq_library_linearizable :
    library_linearizable (M := queue_model NeverEmpty hwq_valid_value) ops hwq_valid_obj.
  Proof.
    set (Σ := #[heapΣ; traceΣ; hwqΣ]).
    intros obj σ config' ts (σ₀ & efs & Hinit_steps) Hadv.
    pose proof (bdgjst_free (Σ:=Σ) hwq_repr
                  (queue_model NeverEmpty hwq_valid_value).(valid_requests)
                  init_hwq ops
                  σ₀ obj efs σ config' ts
                  new_queue_spec (@op_spec)
                  I_lang_hwq_init Hinit_steps Hadv)
      as [Hns HI_lang].
    split; [exact Hns|].
    (* [bdgjst_free]'s [I_lang_hwq ts] conclusion is exactly
       [trace_refines_absq NeverEmpty hwq_valid_value ts]; the trace-level
       refine result then yields [trace_linearizable ts]. *)
    apply refines_absq_trace_linearizable. exact HI_lang.
  Qed.

  Lemma hwq_library_initializable :
    library_initializable init_hwq hwq_valid_obj.
  Proof.
    set (Σ := #[heapΣ; traceΣ; hwqΣ]).
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

  Theorem hwq_library_initializable_linearizable :
    library_initializable_linearizable (M := queue_model NeverEmpty hwq_valid_value) init_hwq ops.
  Proof.
    apply library_initializable_linearizable_iff.
    exists hwq_valid_obj.
    split; [apply hwq_library_initializable | apply hwq_library_linearizable].
  Qed.
End hwq_skeleton_chain.

(* ========================================================================= *)
(* Logically atomic spec for [wrap_op op x y]. Rephrased inside a new
  Section with full [heapGS] + [linearizabilityG] so [atomic.v]'s
  [is_P] / [P_state] / [wrap_op] / [Nlogatom] are well-typed. *)

Section hwq_logatom.
  Context `{!heapGS Σ}.
  Context `{!linearizabilityG (M := queue_model NeverEmpty hwq_valid_value) Σ}.
  Context (sz : Z) (sz_pos : (0 < sz)%Z).

  Local Notation M := (queue_model NeverEmpty hwq_valid_value).

  Theorem hwq_logatom_op_spec (n : nat) γ (x y : val) :
    default default_vr (M.(valid_requests) !! n) y →
    is_P (M := M) ops γ x ⊢
    <<{ ∀∀ s, P_state (M := M) γ s }>>
      wrap_op n (ops !!! n : val) x y @ ↑Nlogatom
    <<{ ∃∃ s' y', P_state (M := M) γ s' ∗
          ⌜default default_rr (M.(request_responses) !! n) s y s' y'⌝ | RET y' }>>.
  Proof.
    apply (logatom_complete_op (init_hwq sz) ops n).
    exact (hwq_library_initializable_linearizable sz sz_pos).
  Qed.

  Corollary hwq_logatom_init_spec :
    {{{ True }}}
      wrap_init (init_hwq sz)
    {{{ γ r, RET r;
        is_P (M := M) ops γ r ∗
        P_state (M := M) γ (s_init : M.(S)) }}}.
  Proof.
    apply (logatom_complete_init (init_hwq sz) ops).
    - done.
    - intros ?. apply fork_free_sequential. compute_done.
    - exact (hwq_library_initializable_linearizable sz sz_pos).
  Qed.
End hwq_logatom.

(* ========================================================================= *)
(* End-to-end logically-atomic client specs, exposing the queue as a
  data structure with enqueue/dequeue operations. Mirrors the
  [hw_queue/aspect.v] and [hw_queue/metaconfig/chain.v] client specs. *)

Section client_specs.
  Context `{!heapGS Σ}.
  Context `{!linearizabilityG (M := queue_model NeverEmpty hwq_valid_value) Σ}.
  Context (sz : Z) (sz_pos : (0 < sz)%Z).

  Local Notation M := (queue_model NeverEmpty hwq_valid_value).

  Definition is_hwq_atomic γ q := is_P (M := M) ops γ q.
  Definition hwq_content γ (ls : list val) := P_state (M := M) γ ls.

  Definition new_queue_wrapper: val := λ: "sz", wrap_init (new_queue "sz").
  Definition enqueue_wrapper : val := λ: "q" "v", wrap_op Push (ops !!! Push : val) "q" "v".
  Definition dequeue_wrapper : val := λ: "q", unwrap (wrap_op Pop (ops !!! Pop : val) "q" #()).

  Lemma new_queue_spec :
    {{{ True }}}
      new_queue_wrapper #sz
    {{{ γ q, RET q; is_hwq_atomic γ q ∗ hwq_content γ [] }}}.
  Proof.
    assert (Hnv : to_val (init_hwq sz) = None) by done.
    assert (Hseq : ∀ σ, sequential (init_hwq sz) σ).
    { intros ?. apply fork_free_sequential. compute_done. }
    pose proof (init_spec_full :=
                  logatom_complete_init _ _ Hnv Hseq
                    (hwq_library_initializable_linearizable sz sz_pos)).
    iIntros (Φ) "HT HΦ".
    wp_lam. iApply (init_spec_full with "HT HΦ").
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
    opose proof (logatom_complete_op _ _ Push
                  (hwq_library_initializable_linearizable sz sz_pos)
                  γ q v _) as op_full_spec.
    { exact Hunboxed. }
    awp_apply (op_full_spec with "His_hwq").
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (s) "Hcontent".
    iAaccIntro with "Hcontent"; first by iIntros "$ !>"; auto.
    iIntros (ls' y) "[Hcontent %Hrr] !>".
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
    opose proof (logatom_complete_op _ _ Pop
                  (hwq_library_initializable_linearizable sz sz_pos)
                  γ q #() _) as op_full_spec.
    { done. }
    awp_apply (op_full_spec with "His_hwq").
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

End client_specs.
