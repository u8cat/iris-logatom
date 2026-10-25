(* refine_new_queue.v: proof of [new_queue_spec] — the init
  obligation for [bdgjst_free].  Establishes the HWQ ghost
  state and invariant atomically when [new_queue #sz] returns. *)

From iris.algebra Require Import auth excl gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy primitive_laws notation proofmode.
From iris_logatom.heap_lang Require Import mgc fork_free.
From iris_logatom.heap_lang.lib Require Import trace.
From iris_logatom.pure_logic Require Import linear adequacy.
From iris_logatom.pure_logic.refine Require Import absq absq_refines_absq0
                                                    absq0_linearizable
                                                    backward_simulation.

From case_studies.hw_queue Require Import impl refine.defs.

Section hwq_skeleton_new_queue.
  Context `{!traceG Σ, !hwqG Σ}.
  Context (sz : Z).
  Hypothesis sz_pos : (0 < sz)%Z.

  (* Alias shared defs so the in-proof syntax matches the original
    monolithic [refine.v].  The [Notation] scope is this Section. *)
  Local Notation Nhwq := Nhwq.
  Local Notation hwq_inv_body := (hwq_inv_body sz).
  Local Notation is_hwq := (is_hwq sz).
  Local Notation hwq_repr := (hwq_repr sz).
  Local Notation init_hwq := (init_hwq sz).

  (* [init_hwq #()] safely allocates the HWQ structure, producing a
    value [obj] and a wand [∀ l, trace_is l [] ={⊤}=∗ is_hwq γ obj l]
    that — given the empty trace at tracer [l] — establishes [is_hwq γ
    obj l] (e.g. by packaging [trace_is] into a user-side invariant
    tied to HWQ's ghost history). *)
  Lemma new_queue_spec :
    ∀ `(!heapGS Σ), init_spec_type hwq_repr NotStuck init_hwq.
  Proof.
    iIntros (Hheap Φ) "_ HΦ".
    rewrite /init_hwq. wp_pures.
    rewrite /new_queue. wp_pures.
    wp_alloc ar as "Har"; first lia.
    wp_pures.
    wp_alloc back as "Hback".
    wp_pures.
    iMod (own_alloc (● (to_opmap ∅) : authR opmapUR)) as (γ) "Hauth".
    { rewrite /to_opmap fmap_empty. apply auth_auth_valid. done. }
    iMod (own_alloc (● (to_svmap ∅) ⋅ ◯ (to_svmap ∅) : authR svmapUR))
      as (γ_sv) "[Hauth_sv Hfrag_sv]".
    { rewrite /to_svmap fmap_empty. apply auth_both_valid_discrete.
      split; [done|done]. }
    iMod (own_alloc (● (to_dqmap ∅) ⋅ ◯ (to_dqmap ∅) : authR dqmapUR))
      as (γ_dq) "[Hauth_dq Hfrag_dq]".
    { rewrite /to_dqmap fmap_empty. apply auth_both_valid_discrete.
      split; [done|done]. }
    iApply ("HΦ" $! γ (#sz, #ar, #back)%V).
    iIntros "!>" (l) "Htrace".
    iMod (inv_alloc Nhwq _ (hwq_inv_body γ γ_sv γ_dq ar back l)
            with "[Har Hback Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq]") as "#Hinv".
    { iNext. rewrite /hwq_inv_body.
      iExists (replicate (Z.to_nat sz) NONEV), 0%Z, [], absq_init, [], ∅, ∅, ∅, ∅.
      iFrame "Har Hback Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
      iPureIntro. split_and!.
      - apply rtcL_refl.
      - by rewrite /trace_of_absq_labels /= filter_nil.
      - apply fs1_sim_init. lia.
      - split.
        + intros τ i d f Hst _. rewrite lookup_empty in Hst. discriminate.
        + intros i v Hlookup. rewrite lookup_empty in Hlookup. discriminate.
      - intros τ d Hlookup. rewrite lookup_empty in Hlookup. discriminate. }
    iModIntro.
    iExists ar, back, γ_sv, γ_dq. iSplit; [done|]. done.
  Qed.

End hwq_skeleton_new_queue.
